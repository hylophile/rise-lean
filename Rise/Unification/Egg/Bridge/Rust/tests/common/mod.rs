use egg_unify::lang::*;
use std::collections::HashMap;

pub fn unify2(s1: &str, s2: &str) -> Result<HashMap<String, String>, String> {
    unify(&format!("{s1}={s2}"))
}

#[allow(dead_code)]
pub fn pp(map: &HashMap<String, String>) {
    for (k, v) in map {
        println!("{}\t = {}", k, v);
    }
}

macro_rules! map {
    ( $( ( $key:expr, $val:expr ) ),* $(,)? ) => {{
        #[allow(unused_mut)]
        let mut map = std::collections::HashMap::<String, String>::new();
        $(
            map.insert($key.to_string(), $val.to_string());
        )*
        map
    }};
}
