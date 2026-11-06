//! `tests/ConLecheTests/OleanTests.lean`'s evaluated checks, over the Rust reader and
//! upstream's committed fixtures (`tests/olean/lib` of the pinned con-leche package,
//! which is only read): every partial read is its part of the full view, each view is
//! the one-memo read's, the imports read off every prefix, the fixtures' facts written
//! by hand from their sources, the emission's input validation, the names of the
//! command line, a bignum's limbs by halves.

use con_ron::olean_fs::StdFs;
use con_ron_core::arena::handle::{EIdx, NIdx};
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::store::{ENodeView, LNodeView, NNodeView, PersTier};
use con_ron_core::frontend::olean::closure::{CEntry, Loaded};
use con_ron_core::frontend::olean::files;
use con_ron_core::frontend::olean::files::OleanFs;
use con_ron_core::frontend::olean::header;
use con_ron_core::frontend::olean::merge;
use con_ron_core::frontend::olean::module;
use con_ron_core::frontend::olean::region;
use con_ron_core::frontend::olean::reads;
use con_ron_core::frontend::olean::spec;
use con_ron_core::frontend::olean::spec::{CEntryF, CKindF, ModDecoded, OleanPins, RdErr};
use con_ron_core::frontend::olean::view;
use con_ron_core::frontend::olean::view::{ModFiles, OLeanLevel};
use con_ron_core::frontend::olean::emit;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::name;
use con_ron_core::ron::hashmap::Eq2;
use con_ron_core::ron::nat;

fn pers() -> PersTier {
    PersTier::empty()
}

/// The fixtures of the pinned package, or `None` where it is not fetched.
fn lib() -> Option<String> {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let out = std::process::Command::new("python3")
        .arg(root.join("scripts/provenance.py"))
        .arg("dir")
        .output()
        .ok()?;
    let dir = String::from_utf8(out.stdout).ok()?.trim().to_string();
    let p = format!("{}/tests/olean/lib", dir);
    if std::path::Path::new(&p).is_dir() {
        Some(p)
    } else {
        eprintln!("no fixtures at {}", p);
        None
    }
}

fn part(p: &str) -> region::Part {
    let cps: Vec<u32> = p.chars().map(|c| c as u32).collect();
    let b = StdFs.read_bin_file(&cps).expect("the file reads");
    region::part_of_bytes(&cps, b).unwrap_or_else(|_| panic!("{} is an .olean", p))
}

fn files_of(lib: &str, m: &str) -> ModFiles {
    let ex = part(&format!("{}/{}.olean", lib, m));
    if std::path::Path::new(&format!("{}/{}.olean.private", lib, m)).exists() {
        ModFiles {
            exported: ex,
            server: Some(part(&format!("{}/{}.olean.server", lib, m))),
            private_part: Some(part(&format!("{}/{}.olean.private", lib, m))),
        }
    } else {
        ModFiles { exported: ex, server: None, private_part: None }
    }
}

fn nm(st: &mut AState, s: &str) -> NIdx {
    let e = PersTier::empty();
    let mut h = st.store.intern_name(&e, NNodeView::Anonymous).ok().unwrap();
    for c in s.split('.') {
        h = st.store.intern_name(&e, NNodeView::Str(h, c.chars().map(|x| x as u32).collect())).ok().unwrap();
    }
    h
}

fn ok_or_panic<T>(x: Result<T, RdErr>, what: &str) -> T {
    match x {
        Ok(v) => v,
        Err(RdErr::Bad) => panic!("{}: it does not read", what),
        Err(RdErr::Err(_)) => panic!("{}: the store's capacity", what),
    }
}

fn entries_eq(a: &[CEntryF<NIdx, EIdx>], b: &[CEntryF<NIdx, EIdx>]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| module::entry_same(x, y))
}

/// A view reads something, and every read of a part of it is its part.
fn agree(what: &str, pk: &OleanPins, st: &mut AState, f: &ModFiles, level: &OLeanLevel) {
    let e = pers();
    let d = ok_or_panic(view::parse_view(pk, &e, &mut st.store, f, level), what);
    assert!(!d.constants.is_empty(), "{}: no constants read", what);
    let l = ok_or_panic(view::read_name_positions(pk, &e, &mut st.store, f, level), what);
    assert!(spec::imports_beq(&l.header.imports, &d.imports), "{}: the imports differ", what);
    assert_eq!(l.consts.len(), d.constants.len(), "{}", what);
    for (x, y) in l.consts.iter().zip(d.constants.iter()) {
        assert!(x.name.eq2(&y.name), "{}: the name positions differ", what);
        let en = ok_or_panic(view::read_entry(pk, &e, &mut st.store, f, level, x.loc), what);
        assert!(module::entry_same(&en, y), "{}: the entry reads differ", what);
    }
    let locs: Vec<u64> = l.consts.iter().map(|p| p.loc).collect();
    let ss = ok_or_panic(view::read_stmts(pk, &e, &mut st.store, f, level, &locs), what);
    assert_eq!(ss.len(), d.constants.len(), "{}", what);
    for (s, c) in ss.iter().zip(d.constants.iter()) {
        let w = spec::c_entry_stmt(c);
        assert!(
            s.name.eq2(&w.name) && s.ty.eq2(&w.ty) && module::nidx_list_eq(&s.level_params, &w.level_params),
            "{}: the statements read differ",
            what
        );
    }
}

fn same_view(a: &ModDecoded, b: &ModDecoded) -> bool {
    spec::imports_beq(&a.imports, &b.imports) && entries_eq(&a.constants, &b.constants)
}

#[test]
fn every_partial_read_is_its_part_and_each_view_the_one_memo_read() {
    let Some(lib) = lib() else { return };
    let e = pers();
    let mut st = AState::empty();
    let pk = spec::olean_pins(&e, &mut st.store).ok().unwrap();
    for m in ["Tiny", "TinyUse", "ClashA", "ClashB", "TinyClassic"] {
        let f = files_of(&lib, m);
        let levels = [OLeanLevel::Exported, OLeanLevel::Server, OLeanLevel::Private];
        for level in &levels {
            agree(m, &pk, &mut st, &f, level);
        }
        let v = ok_or_panic(view::parse_all_views(&pk, &e, &mut st.store, &f), m);
        for level in &levels {
            let d = ok_or_panic(view::parse_view(&pk, &e, &mut st.store, &f, level), m);
            assert!(same_view(&d, view::all_views_at(&v, level)), "{}: differs from the one-memo read", m);
        }
        // an importer holding M.olean alone reads the home's exported view
        let bytes = f.exported.bytes.clone();
        let alone = ModFiles {
            exported: region::part_of_bytes(&Vec::new(), bytes.clone()).ok().unwrap(),
            server: None,
            private_part: None,
        };
        let d = ok_or_panic(view::parse_view(&pk, &e, &mut st.store, &alone, &OLeanLevel::Exported), m);
        assert!(same_view(&d, &v.exported), "{}: the exported file alone", m);
        let mn = nm(&mut st, m);
        assert!(module::check_views(&pk, &e, &mut st.store, &mn, &f, &v).is_ok(), "{}: checkViews", m);
        // the imports off every prefix the walk does not run off, up to the file
        for k in 0..(bytes.len() / 512 + 1) {
            let pre = &bytes[..std::cmp::min(k * 512, bytes.len())];
            if !matches!(header::hdr_walk(pre, region::DATA_START), header::HdrWalk::Short) {
                let imps = ok_or_panic(header::imports_pre(&pk, &e, &mut st.store, pre), m);
                assert!(spec::imports_beq(&imps, &v.exported.imports), "{}: the imports off a prefix", m);
            }
        }
    }
}

fn entry<'a>(cs: &'a [CEntryF<NIdx, EIdx>], st: &mut AState, n: &str) -> Option<&'a CEntryF<NIdx, EIdx>> {
    let h = nm(st, n);
    cs.iter().find(|c| c.name.eq2(&h))
}

fn sort_succ_zero(st: &mut AState) -> EIdx {
    let e = PersTier::empty();
    let z = st.store.intern_level(&e, LNodeView::Zero).ok().unwrap();
    let s = st.store.intern_level(&e, LNodeView::Succ(z)).ok().unwrap();
    st.store.intern(&e, ENodeView::Sort(s)).ok().unwrap()
}

#[test]
fn the_fixtures_facts_from_their_sources() {
    let Some(lib) = lib() else { return };
    let e = pers();
    let mut st = AState::empty();
    let pk = spec::olean_pins(&e, &mut st.store).ok().unwrap();
    // Tiny.lean: `prelude`, no imports; `inductive T | a | b`, `def idT (x : T) : T := x`,
    // `inductive Yes : Prop | intro`, `theorem yes : Yes := Yes.intro`, in a public section
    let f = files_of(&lib, "Tiny");
    let d = ok_or_panic(view::parse_view(&pk, &e, &mut st.store, &f, &OLeanLevel::Private), "Tiny");
    assert!(d.imports.is_empty(), "Tiny imports nothing");
    for n in ["T", "T.a", "T.b", "T.rec", "idT", "Yes", "Yes.intro", "Yes.rec", "yes"] {
        assert!(entry(&d.constants, &mut st, n).is_some(), "Tiny stores {}", n);
    }
    let t = entry(&d.constants, &mut st, "T").unwrap();
    let ty1 = sort_succ_zero(&mut st);
    assert!(t.ty.eq2(&ty1), "T : Type");
    let (ta, tb) = (nm(&mut st, "T.a"), nm(&mut st, "T.b"));
    let tn = nm(&mut st, "T");
    match &t.kind {
        CKindF::Induct(0, 0, all, cs, 0, false, false, false) => {
            assert!(all.len() == 1 && all[0].eq2(&tn));
            assert!(cs.len() == 2 && cs[0].eq2(&ta) && cs[1].eq2(&tb));
        }
        _ => panic!("T is a type of two constructors, no parameters or indices"),
    }
    match &entry(&d.constants, &mut st, "T.b").unwrap().kind {
        CKindF::Ctor(i, 1, 0, 0, false) => assert!(i.eq2(&tn)),
        _ => panic!("T.b is T's constructor 1, no fields"),
    }
    let nil = con_ron_core::arena::handle::LsIdx::of_word(pk.nil.word);
    let c_t = st.store.intern(&e, ENodeView::Const(tn, nil)).ok().unwrap();
    let id_t = entry(&d.constants, &mut st, "idT").unwrap();
    let c_t2 = EIdx::of_word(c_t.word);
    let arrow = st.store.intern(&e, ENodeView::ForallE(c_t2, EIdx::of_word(c_t.word))).ok().unwrap();
    assert!(id_t.ty.eq2(&arrow), "idT : T -> T");
    let b0 = st.store.intern(&e, ENodeView::BVar(0)).ok().unwrap();
    let lam = st.store.intern(&e, ENodeView::Lam(EIdx::of_word(c_t.word), b0)).ok().unwrap();
    match &id_t.kind {
        CKindF::Defn(v, _, s) => {
            assert!(v.eq2(&lam), "idT := fun x => x");
            assert_eq!(s, &vec![115u32, 97, 102, 101]);
        }
        _ => panic!("idT is a definition"),
    }
    let yes = entry(&d.constants, &mut st, "yes").unwrap();
    assert!(matches!(&yes.kind, CKindF::Thm(_, all) if all.len() == 1));
    // the exported level: the theorem and the unexposed definition as axioms of their
    // statements, the inductive types as they are
    let de = ok_or_panic(view::parse_view(&pk, &e, &mut st.store, &f, &OLeanLevel::Exported), "Tiny");
    assert!(matches!(&entry(&de.constants, &mut st, "yes").unwrap().kind, CKindF::Ax(false)));
    assert!(matches!(&entry(&de.constants, &mut st, "idT").unwrap().kind, CKindF::Ax(false)));
    assert!(matches!(&entry(&de.constants, &mut st, "T").unwrap().kind, CKindF::Induct(..)));
    // TinyUse.lean: `public import Tiny`; `def twice (x : T) : T := idT (idT x)`
    let f = files_of(&lib, "TinyUse");
    let d = ok_or_panic(view::parse_view(&pk, &e, &mut st.store, &f, &OLeanLevel::Private), "TinyUse");
    let tiny = nm(&mut st, "Tiny");
    assert!(d.imports.len() == 1 && d.imports[0].module.eq2(&tiny), "TinyUse imports Tiny");
    assert!(d.imports[0].is_exported, "...publicly");
    assert_eq!(d.constants.len(), 2, "TinyUse stores twice and yes'");
    // TinyClassic.lean: no `module`; `inductive U | c`, `def idU (x : U) : U := x`
    let f = files_of(&lib, "TinyClassic");
    let d = ok_or_panic(view::parse_view(&pk, &e, &mut st.store, &f, &OLeanLevel::Private), "TinyClassic");
    assert!(d.imports.is_empty(), "TinyClassic imports nothing");
    for n in ["U", "U.c", "U.rec", "U.recOn", "idU"] {
        assert!(entry(&d.constants, &mut st, n).is_some(), "TinyClassic stores {}", n);
    }
    assert_eq!(d.constants.len(), 5);
}

struct Blocks {
    st: AState,
    pk: OleanPins,
    ty0: EIdx,
    prop: EIdx,
}

impl Blocks {
    fn new() -> Blocks {
        let e = PersTier::empty();
        let mut st = AState::empty();
        let pk = spec::olean_pins(&e, &mut st.store).ok().unwrap();
        let ty0 = sort_succ_zero(&mut st);
        let prop = st.store.intern(&e, ENodeView::Sort(con_ron_core::arena::handle::LIdx::of_word(pk.zero.word))).ok().unwrap();
        Blocks { st, pk, ty0, prop }
    }
    fn n(&mut self, s: &str) -> NIdx {
        nm(&mut self.st, s)
    }
    fn ent(&mut self, s: &str, kind: CKindF<NIdx, EIdx>) -> CEntry {
        let name = self.n(s);
        CEntry {
            c: CEntryF { name, level_params: Vec::new(), ty: EIdx::of_word(self.ty0.word), kind },
            uses: Vec::new(),
        }
    }
    fn ind_i(&mut self, all: &[&str], cs: &[&str], u: bool) -> CEntry {
        let a: Vec<NIdx> = all.iter().map(|x| self.n(x)).collect();
        let c: Vec<NIdx> = cs.iter().map(|x| self.n(x)).collect();
        self.ent("I", CKindF::Induct(0, 0, a, c, 0, false, u, false))
    }
    fn ctor(&mut self, ind: &str, u: bool) -> CEntry {
        let i = self.n(ind);
        self.ent("I.c", CKindF::Ctor(i, 0, 0, 0, u))
    }
    fn rec_i(&mut self, all: &[&str], u: bool) -> CEntry {
        let a: Vec<NIdx> = all.iter().map(|x| self.n(x)).collect();
        self.ent("I.rec", CKindF::Recur(a, 0, 0, 0, 0, Vec::new(), false, u))
    }
    fn blocks(&mut self, cs: Vec<CEntry>) -> Result<(), CheckError> {
        let e = PersTier::empty();
        let m = self.n("M");
        let n = cs.len();
        let mg = merge::merge_all(&self.pk, &e, &self.st.store, vec![Loaded { name: m, constants: cs }]);
        let mg = mg.ok().expect("the merge");
        assert_eq!(mg.order.len(), n);
        emit::blocks_ok(&self.pk, &e, &self.st.store, &mg)
    }
    fn is_err(&mut self, cs: Vec<CEntry>) -> bool {
        matches!(self.blocks(cs), Err(CheckError::Internal(_)))
    }
}

#[test]
fn the_emissions_validation() {
    let mut b = Blocks::new();
    // A constructor its inductive type does not list.
    let (x, y) = (b.ind_i(&["I"], &[], false), b.ctor("I", false));
    assert!(b.is_err(vec![x, y]));
    // A block in order.
    let (x, y, z) = (b.ind_i(&["I"], &["I.c"], false), b.ctor("I", false), b.rec_i(&["I"], false));
    assert!(b.blocks(vec![x, y, z]).is_ok());
    // The same block filtered out, as a whole.
    let (x, y, z) = (b.ind_i(&["I"], &["I.c"], true), b.ctor("I", true), b.rec_i(&["I"], true));
    assert!(b.blocks(vec![x, y, z]).is_ok());
    // A block's `all` that names a theorem.
    let x = b.ind_i(&["I", "bad"], &[], false);
    let t = b.ent("bad", CKindF::Thm(EIdx::of_word(0), Vec::new()));
    assert!(b.is_err(vec![x, t]));
    // A block that does not list its own type, or names one that is not stored.
    let x = b.ind_i(&[], &[], false);
    assert!(b.is_err(vec![x]));
    let x = b.ind_i(&["I", "J"], &[], false);
    assert!(b.is_err(vec![x]));
    // Two types that disagree on the block.
    let x = b.ind_i(&["I", "J"], &[], false);
    let jn = b.n("J");
    let j = b.ent("J", CKindF::Induct(0, 0, vec![jn], Vec::new(), 0, false, false, false));
    assert!(b.is_err(vec![x, j]));
    // A listed constructor not stored, no constructor, or naming another type.
    let x = b.ind_i(&["I"], &["I.c"], false);
    assert!(b.is_err(vec![x]));
    let x = b.ind_i(&["I"], &["I.c"], false);
    let y = b.ent("I.c", CKindF::Ax(false));
    assert!(b.is_err(vec![x, y]));
    // A constructor whose type is not stored, or is no inductive type.
    let y = b.ctor("I", false);
    assert!(b.is_err(vec![y]));
    let (x, y) = (b.ent("I", CKindF::Ax(false)), b.ctor("I", false));
    assert!(b.is_err(vec![x, y]));
    // A recursor of no block, of a block not stored, of no inductive type, not its member's.
    let z = b.rec_i(&[], false);
    assert!(b.is_err(vec![z]));
    let z = b.rec_i(&["I"], false);
    assert!(b.is_err(vec![z]));
    let (x, z) = (b.ent("I", CKindF::Ax(false)), b.rec_i(&["I"], false));
    assert!(b.is_err(vec![x, z]));
    let (x, z) = (b.ind_i(&["I"], &[], false), b.rec_i(&["I", "J"], false));
    assert!(b.is_err(vec![x, z]));
    // Parts of a block of which some are filtered out.
    let (x, y) = (b.ind_i(&["I"], &["I.c"], true), b.ctor("I", false));
    assert!(b.is_err(vec![x, y]));
    let (x, y) = (b.ind_i(&["I"], &["I.c"], false), b.ctor("I", true));
    assert!(b.is_err(vec![x, y]));
    let (x, z) = (b.ind_i(&["I"], &[], true), b.rec_i(&["I"], false));
    assert!(b.is_err(vec![x, z]));
    // A quotient constant outside the package, and a package holding another kind.
    let q = b.ent("Q", CKindF::Quot(vec![116]));
    assert!(b.is_err(vec![q]));
    let (q1, q2) = (b.ent("Quot", CKindF::Quot(vec![116])), b.ent("Quot.mk", CKindF::Ax(false)));
    assert!(b.is_err(vec![q1, q2]));
    let (q1, q2) = (b.ent("Quot", CKindF::Quot(vec![116])), b.ent("Quot.mk", CKindF::Quot(vec![99])));
    assert!(b.blocks(vec![q1, q2]).is_ok());
    let _ = b.prop;
}

fn cps(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

fn rendered(n: &Option<name::Name>) -> Option<String> {
    n.as_ref().map(con_ron::render::name_str)
}

#[test]
fn the_names_of_the_command_line() {
    let got = rendered(&files::parse_mod_name(&cps("Init.Data.Nat")));
    assert_eq!(got.as_deref(), Some("Init.Data.Nat"));
    let n = files::parse_mod_name(&cps("Challenge.\u{ab}12.34\u{bb}.\u{ab}5\u{bb}")).unwrap();
    let cs = name::component_list(&n, Vec::new());
    assert_eq!(cs.len(), 3);
    assert!(matches!(&cs[1], name::NameComponent::Str(s) if s == &cps("12.34")));
    let n = files::parse_mod_name(&cps("\u{ab}a.b\u{bb}")).unwrap();
    assert_eq!(name::component_list(&n, Vec::new()).len(), 1);
    // a component of digits is a number, in a constant's name alone
    let n = files::parse_const_name(&cps("_private.M.0.foo")).unwrap();
    assert!(matches!(&name::component_list(&n, Vec::new())[1], name::NameComponent::Num(0)));
    let n = files::parse_const_name(&cps("\u{ab}0\u{bb}.x")).unwrap();
    assert!(matches!(&name::component_list(&n, Vec::new())[1], name::NameComponent::Str(_)));
    let n = files::parse_mod_name(&cps("123")).unwrap();
    assert!(matches!(&name::component_list(&n, Vec::new())[0], name::NameComponent::Str(_)));
    for bad in ["", "A.", ".A", "A..B", "\u{ab}A", "\u{ab}A\u{bb}B", "A.\u{ab}B", "\u{ab}\u{bb}", "A.\u{ab}\u{bb}"] {
        assert!(files::parse_mod_name(&cps(bad)).is_none(), "{:?}", bad);
    }
    assert_eq!(files::path_join(&cps("a"), &cps("/b")), cps("/b"));
    assert_eq!(files::path_add_extension(&cps("d/x"), &cps("olean")), cps("d/x.olean"));
    assert_eq!(files::path_add_extension(&cps("/x"), &cps("olean")), cps("//x.olean"));
    assert_eq!(files::path_add_extension(&cps("d/.."), &cps("olean")), cps("d/.."));
}

#[test]
fn a_bignum_by_halves() {
    let b: Vec<u8> = (0..800usize).map(|i| ((i * 37 + 11) & 255) as u8).collect();
    for n in [0u64, 1, 15, 16, 17, 33, 64, 99, 100] {
        let f = region::limbs_fold(&b, 0, n, nat::zero());
        assert!(nat::beq(&region::limbs(&b, 0, n), &f), "{}", n);
    }
    assert!(nat::beq(&region::limbs(&b, 8, 91), &region::limbs_fold(&b, 8, 91, nat::zero())));
    // a literal of a million limbs, all ones: `2^(64·n) - 1`, at once (`ron::nat`
    // recurses per limb, so on the checker's stack, `driver::STACK_BYTES`)
    let h = std::thread::Builder::new().stack_size(con_ron::driver::STACK_BYTES).spawn(|| {
        let n = 1_000_000u64;
        let ones = vec![255u8; 8 * n as usize];
        let v = nat::add(&region::limbs(&ones, 0, n), &nat::one());
        assert!(nat::beq(&v, &nat::shift_left(&nat::one(), 64 * n)));
    });
    h.unwrap().join().unwrap();
}

#[test]
fn reads_of_a_part_stay_files_through_the_trait() {
    let Some(lib) = lib() else { return };
    let e = pers();
    let mut st = AState::empty();
    let pk = spec::olean_pins(&e, &mut st.store).ok().unwrap();
    let sp = vec![cps(&lib)];
    let m = nm(&mut st, "TinyUse");
    let imps = files::module_imports(&StdFs, &pk, &e, &mut st.store, &sp, &m).ok().expect("the imports");
    assert_eq!(imps.len(), 1);
    let v = files::read_view(&StdFs, &pk, &e, &mut st.store, &sp, &m, &OLeanLevel::Exported).ok().expect("the view");
    assert!(spec::imports_beq(&imps, &v.imports));
    let (views, expo) = files::read_all_views(&StdFs, &pk, &e, &mut st.store, &sp, &m).ok().expect("a home's read");
    assert_eq!(expo.len(), views.private_part.constants.len());
    // reads' filter: lean4export's
    assert!(!reads::c_kind_skipped::<NIdx, EIdx>(&CKindF::Ax(false)));
    assert!(reads::c_kind_skipped::<NIdx, EIdx>(&CKindF::Ax(true)));
}
