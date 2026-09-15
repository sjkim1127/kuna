//! (kuna DIV-50) Reconcile a renaming input Varnode against input pieces that
//! already occupy the requested storage.
//!
//! `Heritage::guardInput` (`heritage.cc:1953`) can leave write-masked input
//! pieces behind after its concatenating `PIECE` is simplified away.  A later
//! full-width read then collides with those pieces when renaming tries to create
//! a new input.  These pieces are safe to fold with `combineInputVarnodes`
//! because write-masked Varnodes never live on a renaming `VariableStack`.
//!
//! A different shape can collide with a live input.  Destroying that input in
//! the middle of renaming would leave any `VariableStack` entry holding a stale
//! Varnode id, so live inputs are never combined here.  Instead, their bytes are
//! projected with `SUBPIECE`, holes become fresh inputs, and the requested entry
//! value is rebuilt with `PIECE` ops at the function entry.  Existing live input
//! Varnodes remain intact.

use kuna_base::address::Address;
use kuna_base::types::int4;
use kuna_num::opcodes::OpCode;

use crate::context::VarnodeId;
use crate::funcdata::Funcdata;
use crate::varnode::varnode_flags;

/// Create the input value covering `size` bytes at `addr`.
///
/// The ordinary `setInputVarnode` path is tried first.  Write-masked tilings use
/// the destructive DIV-50 combine path; any remaining overlap is reconstructed
/// non-destructively from the existing live inputs.
pub fn new_tiled_input(fd: &mut Funcdata, size: int4, addr: &Address) -> Option<VarnodeId> {
    if size <= 0 {
        return None;
    }
    let candidate = fd.new_varnode(size, addr, None);
    match fd.set_input_varnode(candidate) {
        Ok(vn) => return Some(vn),
        Err(_) => {
            // setInputVarnode raises before mutating, so the candidate is still a
            // free Varnode with no reads.
            let _ = fd.delete_varnode(candidate);
        }
    }
    combine_covered_pieces(fd, size, addr)
        .or_else(|| compose_overlapping_inputs(fd, size, addr))
}

/// Fold the write-masked input pieces covering `[addr, addr+size)` into one
/// full-size input Varnode.
fn combine_covered_pieces(fd: &mut Funcdata, size: int4, addr: &Address) -> Option<VarnodeId> {
    let space = addr.get_space()?.clone();
    let lo = addr.get_offset();
    let hi = lo.checked_add(size as u64)?;

    let mut pieces: Vec<(u64, int4, VarnodeId)> = Vec::new();
    for id in fd.vbank().iter_def_flag(varnode_flags::input) {
        let v = fd.vbank().get(id)?;
        match v.get_addr().get_space() {
            Some(s) if std::rc::Rc::ptr_eq(s, &space) => {}
            _ => continue,
        }
        let voff = v.get_addr().get_offset();
        let vsize = v.get_size();
        let vend = voff.checked_add(vsize as u64)?;
        if vend <= lo || voff >= hi {
            continue; // disjoint from the requested storage
        }
        if voff < lo || vend > hi || !v.is_write_mask() {
            return None; // straddles the request, or is a live input: not ours
        }
        pieces.push((voff, vsize, id));
    }
    if pieces.is_empty() {
        return None;
    }
    pieces.sort_by_key(|p| p.0);

    // Plan the end-to-end tiling before touching the IR: every byte of the request
    // is either a piece or a hole that gets its own input, as guardInput does.
    let mut plan: Vec<(u64, int4, Option<VarnodeId>)> = Vec::new();
    let mut cur = lo;
    for (voff, vsize, id) in pieces {
        if voff < cur {
            return None; // pieces overlap each other
        }
        if voff > cur {
            plan.push((cur, (voff - cur) as int4, None));
        }
        plan.push((voff, vsize, Some(id)));
        cur = voff + vsize as u64;
    }
    if cur < hi {
        plan.push((cur, (hi - cur) as int4, None));
    }

    let mut tiling: Vec<(u64, int4, VarnodeId)> = Vec::new();
    for (off, sz, existing) in plan {
        let vn = match existing {
            Some(id) => id,
            None => {
                let holeaddr = Address::new(std::rc::Rc::clone(&space), off);
                let hole = fd.new_varnode(sz, &holeaddr, None);
                fd.set_input_varnode(hole).ok()?
            }
        };
        tiling.push((off, sz, vn));
    }

    let big_endian = addr.is_big_endian();
    while tiling.len() > 1 {
        let (aoff, asize, avn) = tiling.remove(0);
        let (_boff, bsize, bvn) = tiling.remove(0);
        // combineInputVarnodes takes (most significant, least significant).
        let (vn_hi, vn_lo) = if big_endian { (avn, bvn) } else { (bvn, avn) };
        fd.combine_input_varnodes(vn_hi, vn_lo).ok()?;
        let joinaddr = Address::new(std::rc::Rc::clone(&space), aoff);
        let joined = fd.find_varnode_input(asize + bsize, &joinaddr)?;
        tiling.insert(0, (aoff, asize + bsize, joined));
    }
    let (_, joinedsize, joined) = tiling[0];
    if joinedsize != size {
        return None;
    }
    Some(joined)
}

/// Reconstruct the requested entry value without destroying live input
/// Varnodes.  Existing inputs are sliced as needed, uncovered bytes become new
/// inputs, and the pieces are concatenated at the entry block.
fn compose_overlapping_inputs(fd: &mut Funcdata, size: int4, addr: &Address) -> Option<VarnodeId> {
    let space = addr.get_space()?.clone();
    let lo = addr.get_offset();
    let hi = lo.checked_add(size as u64)?;

    // (covered_lo, covered_hi, source id, source_lo, source_hi)
    let mut covered: Vec<(u64, u64, VarnodeId, u64, u64)> = Vec::new();
    for id in fd.vbank().iter_def_flag(varnode_flags::input) {
        let v = fd.vbank().get(id)?;
        match v.get_addr().get_space() {
            Some(s) if std::rc::Rc::ptr_eq(s, &space) => {}
            _ => continue,
        }
        let source_lo = v.get_addr().get_offset();
        let source_size = v.get_size();
        if source_size <= 0 {
            return None;
        }
        let source_hi = source_lo.checked_add(source_size as u64)?;
        let covered_lo = lo.max(source_lo);
        let covered_hi = hi.min(source_hi);
        if covered_lo < covered_hi {
            covered.push((covered_lo, covered_hi, id, source_lo, source_hi));
        }
    }
    if covered.is_empty() {
        return None;
    }
    covered.sort_by_key(|p| p.0);

    // Plan the full requested range before mutating the IR.  The input bank is
    // supposed to be non-overlapping; fail closed if that invariant is not true.
    let mut plan: Vec<(u64, int4, Option<(VarnodeId, u64, u64)>)> = Vec::new();
    let mut cur = lo;
    for (covered_lo, covered_hi, id, source_lo, source_hi) in covered {
        if covered_lo < cur {
            return None;
        }
        if covered_lo > cur {
            plan.push((cur, (covered_lo - cur) as int4, None));
        }
        plan.push((
            covered_lo,
            (covered_hi - covered_lo) as int4,
            Some((id, source_lo, source_hi)),
        ));
        cur = covered_hi;
    }
    if cur < hi {
        plan.push((cur, (hi - cur) as int4, None));
    }

    let root = fd.bblocks_ref().root?;
    let start = fd.bblocks_ref().get_start_block(root).ok()?;
    let before = fd.bb_op_head(start);
    let opaddr = fd.get_address().clone();
    let big_endian = addr.is_big_endian();

    let mut tiling: Vec<(u64, int4, VarnodeId)> = Vec::with_capacity(plan.len());
    for (off, sz, source) in plan {
        let piece = match source {
            None => {
                let holeaddr = Address::new(std::rc::Rc::clone(&space), off);
                let hole = fd.new_varnode(sz, &holeaddr, None);
                fd.set_input_varnode(hole).ok()?
            }
            Some((id, source_lo, source_hi)) => {
                let segment_hi = off.checked_add(sz as u64)?;
                if off == source_lo && segment_hi == source_hi {
                    id
                } else {
                    let subop = fd.new_op(2, opaddr.clone());
                    fd.op_set_opcode_code(subop, OpCode::CPUI_SUBPIECE);
                    let outaddr = Address::new(std::rc::Rc::clone(&space), off);
                    let out = fd.new_varnode_out(sz, &outaddr, subop).ok()?;
                    fd.op_set_input(subop, id, 0).ok()?;
                    let byte_offset = if big_endian {
                        source_hi.checked_sub(segment_hi)?
                    } else {
                        off.checked_sub(source_lo)?
                    };
                    let offset = fd.new_constant(4, byte_offset);
                    fd.op_set_input(subop, offset, 1).ok()?;
                    fd.op_insert(subop, start, before);
                    out
                }
            }
        };
        tiling.push((off, sz, piece));
    }

    if tiling.len() == 1 {
        return Some(tiling[0].2);
    }
    if !big_endian {
        tiling.reverse();
    }

    let mut value = tiling[0].2;
    let mut value_size = tiling[0].1;
    for (i, &(_, piece_size, piece)) in tiling.iter().enumerate().skip(1) {
        let new_size = value_size.checked_add(piece_size)?;
        let pieceop = fd.new_op(2, opaddr.clone());
        fd.op_set_opcode_code(pieceop, OpCode::CPUI_PIECE);
        let out = if i == tiling.len() - 1 {
            fd.new_varnode_out(size, addr, pieceop).ok()?
        } else {
            fd.new_unique_out(new_size, pieceop).ok()?
        };
        fd.op_set_input(pieceop, value, 0).ok()?;
        fd.op_set_input(pieceop, piece, 1).ok()?;
        fd.op_insert(pieceop, start, before);
        value = out;
        value_size = new_size;
    }
    if value_size != size {
        return None;
    }
    Some(value)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::ArchContext;
    use kuna_base::space::{
        addrspace_flags, spacetype, AddrSpace, AddrSpaceManager, ConstantSpace, UniqueSpace,
    };
    use std::rc::Rc;

    fn build_fd() -> Funcdata {
        let mut manage = AddrSpaceManager::new();
        manage.insert_space(Rc::new(ConstantSpace::new())).unwrap();
        manage.insert_space(Rc::new(UniqueSpace::new(1, 0, false))).unwrap();
        manage
            .insert_space(Rc::new(AddrSpace::new(
                spacetype::IPTR_PROCESSOR,
                "ram",
                false,
                8,
                1,
                2,
                addrspace_flags::hasphysical,
                1,
                1,
            )))
            .unwrap();
        let glb = Rc::new(ArchContext::new(manage));
        let ram = Rc::clone(glb.manage().get_space_by_name("ram").unwrap());
        let mut fd =
            Funcdata::new("func", "func", glb, Address::new(ram, 0x1000), 0x10000000, 0x40)
                .unwrap();
        let root = fd.bblocks_ref().root.unwrap();
        let block = {
            let graph = fd.bblocks_mut();
            let block = graph.new_block_basic(root);
            graph.block_mut(block).set_index(0);
            graph.calc_forward_dominator(root, &[block]);
            block
        };
        assert_eq!(fd.bblocks_ref().get_start_block(root).unwrap(), block);
        fd
    }

    fn ram(fd: &Funcdata) -> Rc<AddrSpace> {
        Rc::clone(fd.get_arch().manage().get_space_by_name("ram").unwrap())
    }

    fn addr(fd: &Funcdata, off: u64) -> Address {
        Address::new(ram(fd), off)
    }

    fn input(fd: &mut Funcdata, off: u64, size: int4) -> VarnodeId {
        let at = addr(fd, off);
        let vn = fd.new_varnode(size, &at, None);
        fd.set_input_varnode(vn).unwrap()
    }

    #[test]
    fn live_input_inside_larger_request_is_preserved() {
        let mut fd = build_fd();
        let live = input(&mut fd, 0x102, 4);
        let request = addr(&fd, 0x100);

        let rebuilt = new_tiled_input(&mut fd, 8, &request).expect("rebuild larger entry value");

        let live_ref = fd.vbank().get(live).expect("live input must survive");
        assert!(live_ref.is_input());
        assert_eq!(live_ref.get_size(), 4);
        assert_eq!(live_ref.get_addr().get_offset(), 0x102);

        let rebuilt_ref = fd.vbank().get(rebuilt).expect("rebuilt value");
        assert!(rebuilt_ref.is_written());
        assert_eq!(rebuilt_ref.get_size(), 8);
        assert_eq!(rebuilt_ref.get_addr().get_offset(), 0x100);
        assert!(fd.find_varnode_input(2, &addr(&fd, 0x100)).is_some());
        assert!(fd.find_varnode_input(2, &addr(&fd, 0x106)).is_some());
    }

    #[test]
    fn request_inside_live_input_uses_subpiece_without_destroying_input() {
        let mut fd = build_fd();
        let live = input(&mut fd, 0x100, 8);
        let request = addr(&fd, 0x102);

        let slice = new_tiled_input(&mut fd, 2, &request).expect("slice existing input");

        assert!(fd.vbank().get(live).expect("live input must survive").is_input());
        let slice_ref = fd.vbank().get(slice).expect("slice value");
        assert!(slice_ref.is_written());
        assert_eq!(slice_ref.get_size(), 2);
        assert_eq!(slice_ref.get_addr().get_offset(), 0x102);

        let def = slice_ref.get_def().expect("slice definition");
        let op = fd.obank().get(def).expect("slice op");
        assert_eq!(op.code(), OpCode::CPUI_SUBPIECE);
        assert_eq!(op.get_in(0), Some(live));
        let offset = op.get_in(1).expect("subpiece offset");
        assert_eq!(fd.vbank().get(offset).expect("offset constant").get_offset(), 2);
    }

    #[test]
    fn straddling_live_input_is_sliced_and_missing_bytes_become_input() {
        let mut fd = build_fd();
        let live = input(&mut fd, 0x100, 4);
        let request = addr(&fd, 0x102);

        let rebuilt = new_tiled_input(&mut fd, 4, &request).expect("rebuild straddled value");

        assert!(fd.vbank().get(live).expect("live input must survive").is_input());
        assert!(fd.find_varnode_input(2, &addr(&fd, 0x104)).is_some());
        let rebuilt_ref = fd.vbank().get(rebuilt).expect("rebuilt value");
        assert!(rebuilt_ref.is_written());
        assert_eq!(rebuilt_ref.get_size(), 4);
        assert_eq!(rebuilt_ref.get_addr().get_offset(), 0x102);

        let piece_def = rebuilt_ref.get_def().expect("piece definition");
        let piece = fd.obank().get(piece_def).expect("piece op");
        assert_eq!(piece.code(), OpCode::CPUI_PIECE);
        let low = piece.get_in(1).expect("little-endian low half");
        let sub_def = fd.vbank().get(low).expect("low half").get_def().expect("subpiece def");
        let sub = fd.obank().get(sub_def).expect("subpiece op");
        assert_eq!(sub.code(), OpCode::CPUI_SUBPIECE);
        assert_eq!(sub.get_in(0), Some(live));
        let offset = sub.get_in(1).expect("subpiece offset");
        assert_eq!(fd.vbank().get(offset).expect("offset constant").get_offset(), 2);
    }
}
