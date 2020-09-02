use rune_testing::{run, Result};
use runestick::{Object, Value};

fn main() -> Result<()> {
    let mut object = Object::<Value>::new();
    object.insert(String::from("Hello"), Value::from(42i64));

    let object: Object<String> = run(
        &["calc"],
        (object,),
        r#"
        fn calc(input) {
            dbg(input["Hello"]);
            input["Hello"] = "World";
            input
        }
        "#,
    )?;

    println!("{:?}", object.get("Hello"));
    Ok(())
}
