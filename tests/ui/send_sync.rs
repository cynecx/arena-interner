use arena_interner::make_interner;

fn is_send<T: Send>(val: T) {}
fn is_sync<T: Sync>(val: T) {}

fn typed() {
    make_interner!(mut interner: str);
    let mut interner = interner.typed_interner::<i32>();
    is_send(&interner); // should fail
    is_sync(&interner); // should fail
    is_send(&mut interner);
    is_sync(&mut interner); // should fail
}

fn main() {
    make_interner!(mut interner: str);
    is_send(&interner); // should fail
    is_sync(&interner); // should fail
    is_send(&mut interner);
    is_sync(&mut interner); // should fail
    typed();
}
