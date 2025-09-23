fn main() {
    // println!("cargo:rustc-link-lib=z3");
    // println!("cargo:rustc-link-search=native=/usr/lib");
    // println!("cargo:rustc-link-arg=-Wl,-rpath,/usr/lib/libz3.so");
    // println!("cargo:rustc-link-search=native=./lib");
    println!("cargo:rustc-link-lib=dylib=z3");
    // println!("cargo:rustc-flags=-C relocation-model=pic");
    // 
}
