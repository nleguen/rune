//! Simple application to test how well the basic Rune infrastructure scales
//! across a number of threads.

use std::io::Write;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use anyhow::{Error, Result};
use rune::termcolor::{ColorChoice, StandardStream};
use rune::{Diagnostics, Value, Vm};
use tokio::time;

#[derive(Debug, Clone, Copy)]
#[allow(dead_code)]
struct Sample {
    ops: f64,
    ops_per_thread: f64,
}

fn main() -> Result<()> {
    let warmup_duration = Duration::from_secs(2);
    let sample_period = Duration::from_millis(100);
    let sample_duration = Duration::from_secs(10);

    let mut args = std::env::args();
    args.next();

    let mut threads: Vec<usize> = Vec::new();

    while let Some(n) = args.next() {
        threads.push(str::parse(&n)?);
    }

    let mut outcomes = Vec::new();

    for n in threads {
        println!("# {}", n);

        let rt = tokio::runtime::Builder::new_multi_thread()
            .worker_threads(n + 1)
            .enable_all()
            .build()?;

        let context = rune_modules::default_context()?;
        let runtime = Arc::new(context.runtime());

        let mut sources = rune::sources! {
            entry => {
                pub async fn main() {}
            }
        };

        let mut diagnostics = Diagnostics::new();

        let result = rune::prepare(&mut sources)
            .with_context(&context)
            .with_diagnostics(&mut diagnostics)
            .build();

        if !diagnostics.is_empty() {
            let mut writer = StandardStream::stderr(ColorChoice::Always);
            diagnostics.emit(&mut writer, &sources)?;
        }

        let count = Arc::new(AtomicU64::new(0));
        let unit = Arc::new(result?);

        let shutdown = Arc::new(AtomicBool::new(false));

        let start = Instant::now();

        let samples = rt.block_on(async move {
            let o = std::io::stdout();
            let mut o = o.lock();

            let mut tasks = Vec::new();

            for _ in 0..n {
                let shutdown = shutdown.clone();
                let runtime = runtime.clone();
                let unit = unit.clone();
                let count = count.clone();

                let task = tokio::spawn(async move {
                    while !shutdown.load(Ordering::SeqCst) {
                        let runtime = runtime.clone();
                        let unit = unit.clone();

                        let execution =
                            Vm::new(runtime.clone(), unit.clone()).send_execute(&["main"], ())?;
                        let value = execution.async_complete().await?;
                        assert!(matches!(value, Value::Unit));
                        let _ = count.fetch_add(1, Ordering::SeqCst);
                    }

                    Ok::<_, Error>(())
                });

                tasks.push(task);
            }

            writeln!(o, "Warming up ({:?})...", warmup_duration)?;
            time::sleep(warmup_duration).await;
            let mut samples = Vec::new();
            count.store(0, Ordering::SeqCst);

            let mut then = Instant::now();

            loop {
                if then.duration_since(start) >= sample_duration {
                    break;
                }

                time::sleep(sample_period).await;

                let now = Instant::now();
                let duration = now.duration_since(then);
                then = now;

                let acc = count.swap(0, Ordering::SeqCst);
                let ops = (acc as f64) / (duration.as_millis() as f64 / 1000.0);
                let ops_per_thread = ops / (n as f64);

                write!(o, ".")?;
                o.flush()?;

                samples.push(Sample {
                    ops,
                    ops_per_thread,
                })
            }

            writeln!(o)?;

            shutdown.store(true, Ordering::SeqCst);

            for task in tasks {
                task.await??;
            }

            Ok::<_, Error>(samples)
        })?;

        rt.shutdown_timeout(Duration::from_secs(5));

        let average =
            samples.iter().map(|s| s.ops_per_thread).sum::<f64>() / (samples.len() as f64);
        outcomes.push((n, average));
    }

    println!("# Summary (<#threads>: <ops/thread>)");

    for (n, ops_per_thread) in outcomes {
        println!("{:3}: {}", n, ops_per_thread);
    }

    Ok(())
}
