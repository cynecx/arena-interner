use arena_interner::make_interner;

fn typed_drop() {
    let a = {
        make_interner!(mut interner: str);
        let t = interner.typed_interner::<i32>();
        t.intern(420)
    };
    println!("{a:?}");
}

fn main() {
    let a = {
        make_interner!(interner: str);
        interner.intern("hello")
    };
    println!("{a:?}");
}
