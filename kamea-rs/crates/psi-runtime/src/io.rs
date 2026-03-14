use std::collections::VecDeque;
use std::io::{self, Read, Write};

/// IO channel abstraction.
pub trait IoChannel {
    fn put(&mut self, byte: u8);
    fn get(&mut self) -> Option<u8>;
    fn flush(&mut self);
}

/// Native: wraps stdin/stdout.
pub struct StdIo;

impl IoChannel for StdIo {
    fn put(&mut self, byte: u8) {
        let _ = io::stdout().write_all(&[byte]);
    }

    fn get(&mut self) -> Option<u8> {
        let mut buf = [0u8; 1];
        match io::stdin().read_exact(&mut buf) {
            Ok(()) => Some(buf[0]),
            Err(_) => None,
        }
    }

    fn flush(&mut self) {
        let _ = io::stdout().flush();
    }
}

/// Buffer IO for WASM and testing.
pub struct BufferIo {
    pub input: VecDeque<u8>,
    pub output: Vec<u8>,
}

impl BufferIo {
    pub fn new() -> Self {
        BufferIo {
            input: VecDeque::new(),
            output: Vec::new(),
        }
    }
}

impl IoChannel for BufferIo {
    fn put(&mut self, byte: u8) {
        self.output.push(byte);
    }

    fn get(&mut self) -> Option<u8> {
        self.input.pop_front()
    }

    fn flush(&mut self) {}
}
