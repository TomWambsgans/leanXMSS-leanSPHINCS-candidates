//! Scoped-thread data parallelism with per-thread CPU accounting.
//!
//! Each party thread sets its own worker count ([`set_threads`]); the helpers split work between
//! that many scoped threads and charge the workers' CPU time back to the calling thread, so
//! [`cpu_seconds`] is the CPU a party has used, whatever its parallelism.

use std::cell::Cell;
use std::sync::atomic::{AtomicUsize, Ordering};

thread_local! {
    static THREADS: Cell<usize> = const { Cell::new(1) };
    static CHILD_CPU: Cell<f64> = const { Cell::new(0.0) };
}

/// The worker count of the helpers called from this thread.
pub fn set_threads(n: usize) {
    THREADS.with(|t| t.set(n.max(1)));
}

pub fn threads() -> usize {
    THREADS.with(|t| t.get())
}

#[repr(C)]
struct Timespec {
    sec: i64,
    nsec: i64,
}

unsafe extern "C" {
    fn clock_gettime(clock: i32, tp: *mut Timespec) -> i32;
}

#[cfg(target_os = "macos")]
const THREAD_CPU_CLOCK: i32 = 16;
#[cfg(not(target_os = "macos"))]
const THREAD_CPU_CLOCK: i32 = 3;

/// CPU seconds of the current thread alone.
pub fn thread_cpu() -> f64 {
    let mut ts = Timespec { sec: 0, nsec: 0 };
    // SAFETY: `ts` is a valid, writable timespec (two 64-bit fields on the supported targets).
    let ok = unsafe { clock_gettime(THREAD_CPU_CLOCK, &mut ts) } == 0;
    if ok { ts.sec as f64 + ts.nsec as f64 * 1e-9 } else { 0.0 }
}

/// CPU seconds used by this thread and the workers it has spawned through these helpers.
pub fn cpu_seconds() -> f64 {
    thread_cpu() + CHILD_CPU.with(|c| c.get())
}

/// Runs `f(i)` for `i` in `0..n` on the worker threads, results in order.
pub fn map<R: Send>(n: usize, f: impl Fn(usize) -> R + Sync) -> Vec<R> {
    let t = threads().min(n);
    if t <= 1 {
        return (0..n).map(f).collect();
    }
    let next = AtomicUsize::new(0);
    let (f, next) = (&f, &next);
    let parts: Vec<(Vec<(usize, R)>, f64)> = std::thread::scope(|s| {
        let hs: Vec<_> = (0..t)
            .map(|_| {
                s.spawn(move || {
                    set_threads(1);
                    let t0 = thread_cpu();
                    let mut out = vec![];
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        if i >= n {
                            break;
                        }
                        out.push((i, f(i)));
                    }
                    (out, thread_cpu() - t0)
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut slots: Vec<Option<R>> = (0..n).map(|_| None).collect();
    for (out, cpu) in parts {
        CHILD_CPU.with(|c| c.set(c.get() + cpu));
        for (i, r) in out {
            slots[i] = Some(r);
        }
    }
    slots.into_iter().map(|r| r.unwrap()).collect()
}

/// Runs `f` on consecutive chunks of `chunk` elements of `data`, on the worker threads.
pub fn for_chunks<T: Send>(data: &mut [T], chunk: usize, f: impl Fn(&mut [T]) + Sync) {
    for_chunks_idx(data, chunk, |_, c| f(c));
}

/// As [`for_chunks`], with the chunk's index.
pub fn for_chunks_idx<T: Send>(data: &mut [T], chunk: usize, f: impl Fn(usize, &mut [T]) + Sync) {
    let chunk = chunk.max(1);
    if threads() <= 1 || data.len() <= chunk {
        data.chunks_mut(chunk).enumerate().for_each(|(i, c)| f(i, c));
        return;
    }
    let cells: Vec<std::sync::Mutex<Option<&mut [T]>>> = data.chunks_mut(chunk).map(|p| std::sync::Mutex::new(Some(p))).collect();
    map(cells.len(), |i| f(i, cells[i].lock().unwrap().take().unwrap()));
}

/// As [`for_chunks_idx`], on two equally long slices cut at the same places.
pub fn for_chunks2_idx<T: Send>(a: &mut [T], b: &mut [T], chunk: usize, f: impl Fn(usize, &mut [T], &mut [T]) + Sync) {
    let chunk = chunk.max(1);
    type Cell<'a, T> = std::sync::Mutex<Option<(&'a mut [T], &'a mut [T])>>;
    let cells: Vec<Cell<T>> = a.chunks_mut(chunk).zip(b.chunks_mut(chunk)).map(|(x, y)| std::sync::Mutex::new(Some((x, y)))).collect();
    map(cells.len(), |i| {
        let (x, y) = cells[i].lock().unwrap().take().unwrap();
        f(i, x, y)
    });
}

/// As [`for_chunks`], on three equally long slices cut at the same places.
pub fn for_chunks3<T: Send>(a: &mut [T], b: &mut [T], c: &mut [T], chunk: usize, f: impl Fn(&mut [T], &mut [T], &mut [T]) + Sync) {
    for_chunks3_idx(a, b, c, chunk, |_, x, y, z| f(x, y, z));
}

/// As [`for_chunks3`], with the chunk's index.
pub fn for_chunks3_idx<T: Send>(a: &mut [T], b: &mut [T], c: &mut [T], chunk: usize, f: impl Fn(usize, &mut [T], &mut [T], &mut [T]) + Sync) {
    let chunk = chunk.max(1);
    type Cell<'a, T> = std::sync::Mutex<Option<(&'a mut [T], &'a mut [T], &'a mut [T])>>;
    let cells: Vec<Cell<T>> = a.chunks_mut(chunk).zip(b.chunks_mut(chunk)).zip(c.chunks_mut(chunk)).map(|((x, y), z)| std::sync::Mutex::new(Some((x, y, z)))).collect();
    map(cells.len(), |i| {
        let (x, y, z) = cells[i].lock().unwrap().take().unwrap();
        f(i, x, y, z)
    });
}

/// Splits `0..n` into about `threads()` contiguous ranges.
pub fn ranges(n: usize) -> Vec<std::ops::Range<usize>> {
    let t = threads().clamp(1, n.max(1));
    let per = n.div_ceil(t);
    (0..t).map(|i| (i * per).min(n)..((i + 1) * per).min(n)).filter(|r| !r.is_empty()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn helpers_cover_everything() {
        set_threads(4);
        assert_eq!(map(100, |i| i * i), (0..100).map(|i| i * i).collect::<Vec<_>>());
        let mut v: Vec<u32> = (0..1000).collect();
        for_chunks(&mut v, 37, |c| c.iter_mut().for_each(|x| *x += 1));
        assert!(v.iter().enumerate().all(|(i, &x)| x == i as u32 + 1));
        let r = ranges(10);
        assert_eq!(r.first().unwrap().start, 0);
        assert_eq!(r.last().unwrap().end, 10);
        assert!(cpu_seconds() >= 0.0);
    }
}
