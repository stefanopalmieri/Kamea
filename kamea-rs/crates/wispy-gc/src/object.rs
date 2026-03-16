//! WispyCons object layout and ObjectModel implementation.
//!
//! Layout (24 bytes total):
//!   Offset 0: [8-byte header]  — MMTk metadata (forwarding ptr, mark bit, etc.)
//!   Offset 8: [8-byte car]     — tagged WispyVal
//!   Offset 16: [8-byte cdr]    — tagged WispyVal
//!
//! ObjectReference points to offset 8 (past the header).
//! ref_to_object_start returns offset 0.

use mmtk::util::copy::*;
use mmtk::util::{Address, ObjectReference};
use mmtk::vm::*;

use crate::vm::WispyVM;

/// Size of the object header in bytes.
pub const HEADER_SIZE: usize = 8;

/// Size of a cons cell including header.
pub const CONS_CELL_SIZE: usize = HEADER_SIZE + 8 + 8; // header + car + cdr = 24

/// Offset from ObjectReference to car field.
pub const CAR_OFFSET: usize = 0; // objref points to car

/// Offset from ObjectReference to cdr field.
pub const CDR_OFFSET: usize = 8;

impl ObjectModel<WispyVM> for WispyVM {
    // All metadata stored in the 8-byte header word.
    const GLOBAL_LOG_BIT_SPEC: VMGlobalLogBitSpec = VMGlobalLogBitSpec::in_header(0);
    const LOCAL_FORWARDING_POINTER_SPEC: VMLocalForwardingPointerSpec =
        VMLocalForwardingPointerSpec::in_header(0);
    const LOCAL_FORWARDING_BITS_SPEC: VMLocalForwardingBitsSpec =
        VMLocalForwardingBitsSpec::in_header(0);
    const LOCAL_MARK_BIT_SPEC: VMLocalMarkBitSpec = VMLocalMarkBitSpec::in_header(0);
    const LOCAL_LOS_MARK_NURSERY_SPEC: VMLocalLOSMarkNurserySpec =
        VMLocalLOSMarkNurserySpec::in_header(0);

    const OBJECT_REF_OFFSET_LOWER_BOUND: isize = HEADER_SIZE as isize;

    fn copy(
        from: ObjectReference,
        semantics: CopySemantics,
        copy_context: &mut GCWorkerCopyContext<WispyVM>,
    ) -> ObjectReference {
        let bytes = Self::get_current_size(from);
        let align = Self::get_align_when_copied(from);
        let offset = Self::get_align_offset_when_copied(from);
        let dst = copy_context.alloc_copy(from, bytes, align, offset, semantics);
        let src_start = Self::ref_to_object_start(from);
        unsafe {
            std::ptr::copy_nonoverlapping(
                src_start.to_ptr::<u8>(),
                dst.to_mut_ptr::<u8>(),
                bytes,
            );
        }
        let new_ref = Self::get_reference_when_copied_to(from, dst);
        copy_context.post_copy(new_ref, bytes, semantics);
        new_ref
    }

    fn copy_to(from: ObjectReference, to: ObjectReference, _region: Address) -> Address {
        let bytes = Self::get_current_size(from);
        let src_start = Self::ref_to_object_start(from);
        let dst_start = Self::ref_to_object_start(to);
        unsafe {
            std::ptr::copy_nonoverlapping(
                src_start.to_ptr::<u8>(),
                dst_start.to_mut_ptr::<u8>(),
                bytes,
            );
        }
        dst_start + bytes
    }

    fn get_reference_when_copied_to(_from: ObjectReference, to: Address) -> ObjectReference {
        // `to` is the allocation start (header). ObjectReference points past header.
        ObjectReference::from_raw_address(to + HEADER_SIZE).unwrap()
    }

    fn get_current_size(_object: ObjectReference) -> usize {
        CONS_CELL_SIZE
    }

    fn get_size_when_copied(_object: ObjectReference) -> usize {
        CONS_CELL_SIZE
    }

    fn get_align_when_copied(_object: ObjectReference) -> usize {
        8 // word-aligned
    }

    fn get_align_offset_when_copied(_object: ObjectReference) -> usize {
        0
    }

    fn get_type_descriptor(_reference: ObjectReference) -> &'static [i8] {
        // WispY has only one object type: cons cell.
        &[]
    }

    fn ref_to_object_start(object: ObjectReference) -> Address {
        object.to_raw_address() - HEADER_SIZE
    }

    fn ref_to_header(object: ObjectReference) -> Address {
        object.to_raw_address() - HEADER_SIZE
    }

    fn dump_object(object: ObjectReference) {
        let addr = object.to_raw_address();
        let car: i64 = unsafe { addr.load::<i64>() };
        let cdr: i64 = unsafe { (addr + 8usize).load::<i64>() };
        eprintln!("WispyCons @ {:?}: car={}, cdr={}", addr, car, cdr);
    }
}
