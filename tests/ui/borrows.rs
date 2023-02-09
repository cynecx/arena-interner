use arena_interner::make_interner;

fn borrow_two() {
    make_interner!(mut interner);
    let t1 = interner.typed_interner::<i32>();
    let t2 = interner.typed_interner::<i32>();
    let _a = t1.intern(1);
    let _b = t2.intern(1);
}

fn main() {
    make_interner!(mut interner);
    let _a = interner.intern("1");
    let t = interner.typed_interner::<i32>();
    let _b = t.intern(1);
    let _c = interner.intern("1");
    let _d = t.intern(1);
}
