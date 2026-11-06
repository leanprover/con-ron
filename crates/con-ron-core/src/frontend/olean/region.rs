//! `ConLeche/Frontend/Olean/Region.lean` — the byte region (task #142).
//!
//! An `.olean` file is a compacted region: the runtime's object graph with
//! every pointer an absolute address.  **Nothing in the files is trusted**:
//! the files are read into memory, laid end to end, and every object the
//! reader visits is located, bounds-checked and read field by field.
//!
//! ## Deviations
//!
//! * **`Nat` is `u64`** for a location and for what is compared with one.  A
//!   location lies inside a region, which is at most three files of less than
//!   2^60 bytes (`part_of_bytes`), so that `g + 8 + 8 * i` never overflows.  A
//!   length read off the file can be anything: those sums go through
//!   [`sat_add`] and [`sat_mul8`], which stop at `u64::MAX`, above every size,
//!   so that a comparison with a size answers as `Nat`'s does.
//! * **`Region` does not hold its bytes**: every reader takes `bs: &[u8]` beside
//!   `r: &Region`, so that `Region.single` is no copy of the file.  A record with
//!   a borrowed field made Aeneas run out of memory on the smallest loop over it,
//!   40 GB on `region_loc_go`.  `Region.ofParts` has to concatenate, so it returns
//!   the bytes with the record, a [`RegionBuf`].
//! * **A `Nat` field saturates** (`region_nat_sat`): a number that does not fit
//!   a `u64` (only a crafted file holds one) comes back as `u64::MAX`, and the
//!   callers turn that into the `Native` decline (`spec::skel_fits`,
//!   `spec::nat_word`), at the place where the Lean's `Nat` goes on to be used.
//! * **A string is a `Vec<u32>`** of code points (§3.3); `scan_fast::utf8_decode`
//!   is `String.fromUTF8?`.
//! * `Region.down_lt`, a theorem, is not ported (§3.1).

use crate::frontend::scan_fast;
use crate::frontend::text;
use crate::kernel::core_types;
use crate::kernel::core_types::CheckError;
use crate::kernel::name;
use crate::ron::nat;
use crate::ron::nat::Nat;

/// con-leche: none — `Nat`'s `+` on a sum one of whose terms was read off a
/// file: it stops at `u64::MAX`, above every size it is compared with (module
/// note).
#[inline(always)]
pub fn sat_add(a: u64, b: u64) -> u64 {
    if a > u64::MAX - b {
        u64::MAX
    } else {
        a + b
    }
}

/// con-leche: none — `Nat`'s `8 * n`, as [`sat_add`].
#[inline(always)]
pub fn sat_mul8(n: u64) -> u64 {
    if n > u64::MAX / 8 {
        u64::MAX
    } else {
        8 * n
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:67-68 rdU8
/// A byte; past the end, `0`.
#[inline(always)]
pub fn rd_u8(b: &[u8], i: u64) -> u8 {
    if i < (b.len() as u64) {
        b[i as usize]
    } else {
        0
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:70-72 rdU32
/// Four bytes, little-endian.
#[inline(always)]
pub fn rd_u32(b: &[u8], i: u64) -> u32 {
    (rd_u8(b, i) as u32)
        | ((rd_u8(b, i + 1) as u32) << 8)
        | ((rd_u8(b, i + 2) as u32) << 16)
        | ((rd_u8(b, i + 3) as u32) << 24)
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:74-81 rdU64
/// One bounds check for the eight bytes.  The test is `i ≤ size - 8`, not
/// `i + 8 ≤ size`, so that it needs no sum.
#[inline(always)]
pub fn rd_u64(b: &[u8], i: u64) -> u64 {
    let n = b.len() as u64;
    if 8 <= n && i <= n - 8 {
        let k = i as usize;
        (b[k] as u64)
            | ((b[k + 1] as u64) << 8)
            | ((b[k + 2] as u64) << 16)
            | ((b[k + 3] as u64) << 24)
            | ((b[k + 4] as u64) << 32)
            | ((b[k + 5] as u64) << 40)
            | ((b[k + 6] as u64) << 48)
            | ((b[k + 7] as u64) << 56)
    } else {
        0
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:85-89 Part
/// One file of a module: its bytes and the address its byte `0` stands for.
pub struct Part {
    pub base: u64,
    pub bytes: Vec<u8>,
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:91-93 headerSize
pub const HEADER_SIZE: u64 = 88;
/// con-leche: ConLeche/Frontend/Olean/Region.lean:94-94 dataStart
pub const DATA_START: u64 = 96;

/// con-leche: none — the port's cap on a file's size, the reason a location
/// fits its word (module note).  2^60 bytes is an exbibyte.
pub const PART_MAX: u64 = 1 << 60;

/// con-leche: ConLeche/Frontend/Olean/Region.lean:96-119 Part.ofBytes
/// **The header, validated.**  Deviation: a file past [`PART_MAX`] is the
/// `Native` decline before anything else is looked at; the path is rendered
/// (`display_path`, task #131), which prints an ordinary path as it is.
pub fn part_of_bytes(path: &Vec<u32>, b: Vec<u8>) -> Result<Part, CheckError> {
    let size = b.len() as u64;
    if PART_MAX <= size {
        return Err(core_types::native(path_msg(path, { const M: [u32; 43] = [58, 32, 97, 110, 32, 46, 111, 108, 101, 97, 110, 32, 102, 105, 108, 101, 32, 112, 97, 115, 116, 32, 116, 104, 101, 32, 112, 111, 114, 116, 39, 115, 32, 115, 105, 122, 101, 32, 108, 105, 109, 105, 116]; crate::kernel::core_types::code_points(&M) })));
    }
    if size < DATA_START {
        let m = path_msg(path, { const M: [u32; 13] = [58, 32, 116, 114, 117, 110, 99, 97, 116, 101, 100, 58, 32]; crate::kernel::core_types::code_points(&M) });
        let m = text::cat(m, &text::u64_str(size));
        let m = text::cat(m, &{ const M: [u32; 28] = [32, 98, 121, 116, 101, 115, 44, 32, 97, 110, 32, 46, 111, 108, 101, 97, 110, 32, 104, 101, 97, 100, 101, 114, 32, 105, 115, 32]; crate::kernel::core_types::code_points(&M) });
        return Err(core_types::internal(text::cat(m, &text::u64_str(DATA_START))));
    }
    if !(b[0] == 111 && b[1] == 108 && b[2] == 101 && b[3] == 97 && b[4] == 110) {
        let shown: Vec<u32> = match scan_fast::utf8_decode(&b, 0, 5) {
            Some(s) => s,
            None => { const M: [u32; 1] = [63]; crate::kernel::core_types::code_points(&M) },
        };
        let m = path_msg(path, { const M: [u32; 42] = [58, 32, 110, 111, 116, 32, 97, 110, 32, 46, 111, 108, 101, 97, 110, 32, 102, 105, 108, 101, 58, 32, 116, 104, 101, 32, 102, 105, 114, 115, 116, 32, 98, 121, 116, 101, 115, 32, 97, 114, 101, 32]; crate::kernel::core_types::code_points(&M) });
        let m = text::cat(m, &name::display_str(&shown));
        return Err(core_types::internal(text::cat(m, &{ const M: [u32; 18] = [44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 96, 111, 108, 101, 97, 110, 96]; crate::kernel::core_types::code_points(&M) })));
    }
    let ver = rd_u8(&b, 5);
    if ver != 2 {
        let m = path_msg(path, { const M: [u32; 24] = [58, 32, 46, 111, 108, 101, 97, 110, 32, 102, 111, 114, 109, 97, 116, 32, 118, 101, 114, 115, 105, 111, 110, 32]; crate::kernel::core_types::code_points(&M) });
        let m = text::cat(m, &text::u64_str(ver as u64));
        return Err(core_types::not_implemented(text::cat(m, &{ const M: [u32; 30] = [32, 40, 116, 104, 105, 115, 32, 114, 101, 97, 100, 101, 114, 32, 114, 101, 97, 100, 115, 32, 118, 101, 114, 115, 105, 111, 110, 32, 50, 41]; crate::kernel::core_types::code_points(&M) })));
    }
    if rd_u8(&b, 6) & 1 != 1 {
        return Err(core_types::not_implemented(path_msg(path, { const M: [u32; 29] = [58, 32, 46, 111, 108, 101, 97, 110, 32, 119, 105, 116, 104, 32, 110, 111, 110, 45, 71, 77, 80, 32, 98, 105, 103, 110, 117, 109, 115]; crate::kernel::core_types::code_points(&M) })));
    }
    if size % 8 != 0 {
        return Err(core_types::internal(path_msg(path, { const M: [u32; 29] = [58, 32, 110, 111, 116, 32, 97, 32, 119, 104, 111, 108, 101, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 119, 111, 114, 100, 115]; crate::kernel::core_types::code_points(&M) })));
    }
    let base = rd_u64(&b, 80);
    if !(base % 8 == 0 && base <= u64::MAX - size) {
        return Err(core_types::internal(path_msg(path, { const M: [u32; 18] = [58, 32, 98, 97, 100, 32, 98, 97, 115, 101, 32, 97, 100, 100, 114, 101, 115, 115]; crate::kernel::core_types::code_points(&M) })));
    }
    Ok(Part { base, bytes: b })
}

/// con-leche: none — the `{path}: …` of `Part.ofBytes`'s messages
/// A path and the rest of a message.
pub fn path_msg(path: &Vec<u32>, rest: Vec<u32>) -> Vec<u32> {
    text::cat(display_path(path), &rest)
}

/// con-leche: none — con-leche prints a path raw
/// A path, for a message: as it is when it holds nothing a display must escape,
/// else `display_str` of it.  The driver's `render::display_path` in the core,
/// for the messages the reader makes (task #131's deviation).
pub fn display_path(p: &Vec<u32>) -> Vec<u32> {
    if path_is_plain(p) {
        crate::kernel::expr::str_copy(p)
    } else {
        name::display_str(p)
    }
}

/// con-leche: none — `display_path`'s test
pub fn path_is_plain(p: &Vec<u32>) -> bool {
    let n = p.len();
    let mut i = 0usize;
    while i < n {
        let c = p[i];
        if c == 92 || c == 34 || name::display_unsafe_char(c) {
            return false;
        }
        i += 1;
    }
    true
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:121-122 Part.moduleDataAddr
/// The address of a file's `ModuleData` (the slot after the header).
pub fn part_module_data_addr(p: &Part) -> u64 {
    rd_u64(&p.bytes, HEADER_SIZE)
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:126-131 Seg
/// One file inside the region.
pub struct Seg {
    pub base: u64,
    pub off: u64,
    pub size: u64,
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:133-137 Region
/// **The address space of one module**: where each file is.  Deviation: the
/// bytes are not in the record; every reader takes them beside it (module note).
pub struct Region {
    pub segs: Vec<Seg>,
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:147-157 Region.ofParts
/// What `Region.ofParts` builds: the files' bytes laid end to end and where
/// each one is.
pub struct RegionBuf {
    pub bytes: Vec<u8>,
    pub region: Region,
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:139-140 Region.single
/// The region of one file.
pub fn region_single(p: &Part) -> Region {
    let mut segs: Vec<Seg> = Vec::with_capacity(1);
    segs.push(Seg { base: p.base, off: 0, size: p.bytes.len() as u64 });
    Region { segs }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:142-145 partsOrdered
/// One step of the walk: the two files do not overlap, in increasing address
/// order.  `part_of_bytes` keeps a file's base plus its size below 2^64, so that the
/// sum does not saturate.
pub fn parts_ordered(a: &Part, b: &Part) -> bool {
    sat_add(a.base, a.bytes.len() as u64) <= b.base
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:147-157 Region.ofParts
/// One file onto a region under construction.
pub fn region_push(bytes: Vec<u8>, segs: Vec<Seg>, p: &Part) -> (Vec<u8>, Vec<Seg>) {
    let mut bytes = bytes;
    let mut segs = segs;
    let off = bytes.len() as u64;
    bytes.extend_from_slice(&p.bytes);
    segs.push(Seg { base: p.base, off, size: p.bytes.len() as u64 });
    (bytes, segs)
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:147-157 Region.ofParts
/// The region of two files of a module, in increasing address order.  Deviation:
/// upstream's array is the two spellings `region_of_parts2`, `region_of_parts3`; a
/// list of borrows is outside the extraction's nested-borrow rule (F4).
pub fn region_of_parts2(a: &Part, b: &Part) -> Result<RegionBuf, CheckError> {
    if !parts_ordered(a, b) {
        return Err(core_types::internal({ const M: [u32; 36] = [116, 104, 101, 32, 46, 111, 108, 101, 97, 110, 32, 102, 105, 108, 101, 115, 32, 111, 102, 32, 97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 118, 101, 114, 108, 97, 112]; crate::kernel::core_types::code_points(&M) }));
    }
    let (bytes, segs) = region_push(Vec::with_capacity(a.bytes.len() + b.bytes.len()), Vec::with_capacity(2), a);
    let (bytes, segs) = region_push(bytes, segs, b);
    Ok(RegionBuf { bytes, region: Region { segs } })
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:147-157 Region.ofParts
/// The region of all three files of a module, in increasing address order.
pub fn region_of_parts3(a: &Part, b: &Part, c: &Part) -> Result<RegionBuf, CheckError> {
    if !(parts_ordered(a, b) && parts_ordered(b, c)) {
        return Err(core_types::internal({ const M: [u32; 36] = [116, 104, 101, 32, 46, 111, 108, 101, 97, 110, 32, 102, 105, 108, 101, 115, 32, 111, 102, 32, 97, 32, 109, 111, 100, 117, 108, 101, 32, 111, 118, 101, 114, 108, 97, 112]; crate::kernel::core_types::code_points(&M) }));
    }
    let (bytes, segs) = region_push(Vec::with_capacity(a.bytes.len() + b.bytes.len() + c.bytes.len()), Vec::with_capacity(3), a);
    let (bytes, segs) = region_push(bytes, segs, b);
    let (bytes, segs) = region_push(bytes, segs, c);
    Ok(RegionBuf { bytes, region: Region { segs } })
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:159-161 isScalar
/// **The scalar test**: a value that is not a pointer is `(n <<< 1) ||| 1`.
#[inline(always)]
pub fn is_scalar(v: u64) -> bool {
    v & 1 == 1
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:163-164 unbox
/// The value of a boxed scalar.
#[inline(always)]
pub fn unbox(v: u64) -> u64 {
    v >> 1
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:166-179 Region.locGo
/// `Region.loc`'s search, from the last file; `0` when no file holds an object
/// at the address.
pub fn region_loc_go(r: &Region, a: u64, i: usize) -> u64 {
    let mut i = i;
    while i > 0 {
        i -= 1;
        let base = r.segs[i].base;
        let size = r.segs[i].size;
        if base <= a && a - base < size {
            let o = a - base;
            let g = r.segs[i].off + o;
            if g % 8 == 0 && DATA_START <= o && o + 8 <= size {
                return g;
            } else {
                return 0;
            }
        }
    }
    0
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:181-189 Region.loc
/// **The location of the object at an address.**  A scalar is no address.
#[inline(always)]
pub fn region_loc(r: &Region, a: u64) -> Option<u64> {
    if is_scalar(a) {
        None
    } else {
        let g = region_loc_go(r, a, r.segs.len());
        if g == 0 {
            None
        } else {
            Some(g)
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:191-198 Region.endGo
/// `Region.fileEnd`'s search.
pub fn region_end_go(r: &Region, g: u64, i: usize) -> u64 {
    let mut i = i;
    while i > 0 {
        i -= 1;
        let off = r.segs[i].off;
        let e = off + r.segs[i].size;
        if off <= g && g < e {
            return e;
        }
    }
    0
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:200-202 Region.fileEnd
/// **The end of the file a location is in.**
#[inline(always)]
pub fn region_file_end(r: &Region, g: u64) -> u64 {
    region_end_go(r, g, r.segs.len())
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:204-209 Region.down
/// **A pointer the object at `g` holds**, followed: the location of the object
/// it points to, which must lie below `g`.
#[inline(always)]
pub fn region_down(r: &Region, g: u64, v: u64) -> Option<u64> {
    match region_loc(r, v) {
        Some(c) => {
            if c < g {
                Some(c)
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:220-223 Region.okPtr
/// A pointer field not followed yet: a scalar, or a pointer below `g`.
#[inline(always)]
pub fn region_ok_ptr(r: &Region, g: u64, v: u64) -> bool {
    if is_scalar(v) {
        true
    } else {
        match region_down(r, g, v) {
            Some(_) => true,
            None => false,
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:227-228 Region.tag
/// The header's tag byte.
#[inline(always)]
pub fn region_tag(bs: &[u8], g: u64) -> u64 {
    rd_u8(bs, g + 7) as u64
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:230-231 Region.nobjs
/// The header's `m_other` byte.
#[inline(always)]
pub fn region_nobjs(bs: &[u8], g: u64) -> u64 {
    rd_u8(bs, g + 6) as u64
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:233-235 Region.fits
/// A constructor object's pointer fields lie inside its file.
#[inline(always)]
pub fn region_fits(bs: &[u8], r: &Region, g: u64) -> bool {
    g + 8 + 8 * region_nobjs(bs, g) <= region_file_end(r, g)
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:237-238 Region.fld
/// **A constructor's pointer field** `i`.
#[inline(always)]
pub fn region_fld(bs: &[u8], g: u64, i: u64) -> u64 {
    rd_u64(bs, g + 8 + 8 * i)
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:240-243 Region.ptrFld
/// A pointer field, checked and returned as it is.
#[inline(always)]
pub fn region_ptr_fld(bs: &[u8], r: &Region, g: u64, i: u64) -> Option<u64> {
    let v = region_fld(bs, g, i);
    if region_ok_ptr(r, g, v) {
        Some(v)
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:245-250 Region.u8
/// A one-byte scalar field: byte `k` of the scalar area.
pub fn region_u8(bs: &[u8], r: &Region, g: u64, k: u64) -> Option<u8> {
    let i = g + 8 + 8 * region_nobjs(bs, g) + k;
    if i < region_file_end(r, g) {
        Some(rd_u8(bs, i))
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:252-255 Region.u32
/// A four-byte scalar field at byte `k` of the scalar area.
pub fn region_u32(bs: &[u8], r: &Region, g: u64, k: u64) -> Option<u32> {
    let i = g + 8 + 8 * region_nobjs(bs, g) + k;
    if i + 4 <= region_file_end(r, g) {
        Some(rd_u32(bs, i))
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:257-262 Region.bool
/// A one-byte `Bool` scalar.
pub fn region_bool(bs: &[u8], r: &Region, g: u64, k: u64) -> Option<bool> {
    match region_u8(bs, r, g, k) {
        Some(0) => Some(false),
        Some(1) => Some(true),
        _ => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:264-266 Region.isCtor
/// A constructor of tag `t` with `n` pointer fields, inside its file.
#[inline(always)]
pub fn region_is_ctor(bs: &[u8], r: &Region, g: u64, t: u64, n: u64) -> bool {
    region_tag(bs, g) == t && region_nobjs(bs, g) == n && region_fits(bs, r, g)
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:270-270 tagArray
pub const TAG_ARRAY: u64 = 246;
/// con-leche: ConLeche/Frontend/Olean/Region.lean:271-271 tagString
pub const TAG_STRING: u64 = 249;
/// con-leche: ConLeche/Frontend/Olean/Region.lean:272-272 tagMPZ
pub const TAG_MPZ: u64 = 250;

/// con-leche: ConLeche/Frontend/Olean/Region.lean:274-279 limbsFold
/// A few limbs of a bignum, most significant first into the accumulator.
pub fn limbs_fold(b: &[u8], lo: u64, i: u64, acc: Nat) -> Nat {
    let mut i = i;
    let mut acc = acc;
    while i > 0 {
        i -= 1;
        let top = nat::shift_left(&acc, 64);
        acc = nat::add(&top, &nat::from_u64(rd_u64(b, lo + 8 * i)));
    }
    acc
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:281-294 limbs
/// **The value of the `n` limbs at `lo`**, by halves: linear per level of the
/// halving, where the fold alone is quadratic in the literal's length.
pub fn limbs(b: &[u8], lo: u64, n: u64) -> Nat {
    if n <= 16 {
        limbs_fold(b, lo, n, nat::zero())
    } else {
        let k = n / 2;
        let low = limbs(b, lo, k);
        let high = limbs(b, lo + 8 * k, n - k);
        nat::add(&low, &nat::shift_left(&high, 64 * k))
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:296-307 Region.mpzAt
/// **A bignum object** at location `c`, the address `v` pointing at it.  The
/// address sum wraps, as `UInt64`'s does.
pub fn region_mpz_at(bs: &[u8], r: &Region, c: u64, v: u64) -> Option<Nat> {
    if region_tag(bs, c) == TAG_MPZ {
        let size = rd_u32(bs, c + 12);
        let n = size as u64;
        if size < (1u32 << 31)
            && rd_u64(bs, c + 16) == v.wrapping_add(24)
            && c + 24 + 8 * n <= region_file_end(r, c)
        {
            Some(limbs(bs, c + 24, n))
        } else {
            None
        }
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:309-315 Region.natP
/// **A `Nat` the object at `g` holds**: a boxed scalar, or a bignum below `g`.
pub fn region_nat_p(bs: &[u8], r: &Region, g: u64, v: u64) -> Option<Nat> {
    if is_scalar(v) {
        Some(nat::from_u64(unbox(v)))
    } else {
        match region_down(r, g, v) {
            Some(c) => region_mpz_at(bs, r, c, v),
            None => None,
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:309-315 Region.natP
/// `Region.natP` where the value will be a machine word: the boxed scalar needs
/// no `Nat`, and a value that does not fit comes back as `u64::MAX` (module
/// note).
#[inline(always)]
pub fn region_nat_sat(bs: &[u8], r: &Region, g: u64, v: u64) -> Option<u64> {
    if is_scalar(v) {
        Some(unbox(v))
    } else {
        match region_down(r, g, v) {
            Some(c) => match region_mpz_at(bs, r, c, v) {
                Some(n) => Some(nat_saturate(&n)),
                None => None,
            },
            None => None,
        }
    }
}

/// con-leche: none — a `Nat` as a word, `u64::MAX` when it does not fit (module note)
pub fn nat_saturate(n: &Nat) -> u64 {
    match nat::to_u64(n) {
        Some(k) => k,
        None => u64::MAX,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:317-326 Region.strAt
/// **A string object** at location `c`, which must be valid UTF-8.
pub fn region_str_at(bs: &[u8], r: &Region, c: u64) -> Option<Vec<u32>> {
    if region_tag(bs, c) == TAG_STRING {
        let sz = rd_u64(bs, c + 8);
        let fe = region_file_end(r, c);
        if 1 <= sz && sat_add(c + 32, sz) <= fe && rd_u8(bs, c + 32 + sz - 1) == 0 {
            scan_fast::utf8_decode(bs, (c + 32) as usize, (c + 32 + sz - 1) as usize)
        } else {
            None
        }
    } else {
        None
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:328-332 Region.strP
/// **A `String` the object at `g` holds.**
pub fn region_str_p(bs: &[u8], r: &Region, g: u64, v: u64) -> Option<Vec<u32>> {
    match region_down(r, g, v) {
        Some(c) => region_str_at(bs, r, c),
        None => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:334-342 Region.objArrayGo
/// `Region.objArray`'s loop over the elements.
pub fn region_obj_array_go(bs: &[u8], r: &Region, c: u64, lo: u64, n: u64, acc: Vec<u64>) -> Option<Vec<u64>> {
    let mut acc = acc;
    let mut i = 0u64;
    while i < n {
        match region_down(r, c, rd_u64(bs, lo + 8 * i)) {
            Some(e) => acc.push(e),
            None => return None,
        }
        i += 1;
    }
    Some(acc)
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:344-355 Region.objArray
/// **An `Array` of objects the object at `g` holds**: the elements' locations,
/// each below the array.
pub fn region_obj_array(bs: &[u8], r: &Region, g: u64, v: u64) -> Option<Vec<u64>> {
    match region_down(r, g, v) {
        Some(c) => {
            if region_tag(bs, c) == TAG_ARRAY {
                let n = rd_u64(bs, c + 8);
                if sat_add(c + 24, sat_mul8(n)) <= region_file_end(r, c) {
                    region_obj_array_go(bs, r, c, c + 24, n, Vec::with_capacity(n as usize))
                } else {
                    None
                }
            } else {
                None
            }
        }
        None => None,
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:357-371 Region.listGo
/// `Region.list`'s walk over the cells: `[]` is the scalar `0`, `a :: as` the
/// constructor `1` with two fields.
pub fn region_list_go(bs: &[u8], r: &Region, c: u64, acc: Vec<u64>) -> Option<Vec<u64>> {
    let mut c = c;
    let mut acc = acc;
    loop {
        if !region_is_ctor(bs, r, c, 1, 2) {
            return None;
        }
        match region_ptr_fld(bs, r, c, 0) {
            None => return None,
            Some(hd) => {
                acc.push(hd);
                let tl = region_fld(bs, c, 1);
                if tl == 1 {
                    return Some(acc);
                }
                match region_down(r, c, tl) {
                    Some(c2) => c = c2,
                    None => return None,
                }
            }
        }
    }
}

/// con-leche: ConLeche/Frontend/Olean/Region.lean:373-379 Region.list
/// **A `List` the object at `g` holds**: its elements, each a scalar or a
/// pointer below its cell.
pub fn region_list(bs: &[u8], r: &Region, g: u64, v: u64) -> Option<Vec<u64>> {
    if v == 1 {
        Some(Vec::new())
    } else {
        match region_down(r, g, v) {
            Some(c) => region_list_go(bs, r, c, Vec::new()),
            None => None,
        }
    }
}
