/*
 * Copyright 2024 Cybernetica AS
 * 
 * Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:
 * 1. Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the copyright holder nor the names of its contributors may be used to endorse or promote products derived from this software without specific prior written permission.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS “AS IS” AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

use std::{
    alloc::Layout,
    alloc::{alloc, dealloc},
    cell::Cell,
    marker::PhantomData,
    mem::MaybeUninit,
    ptr::NonNull,
};

#[inline(never)]
#[cold]
fn oom() -> ! {
    panic!("Stack out of memory")
}

pub struct StackMemory {
    data: *mut u8,
    layout: Layout,
    locked: Cell<bool>,
}

impl StackMemory {
    pub fn new(max_capacity: usize) -> Self {
        // NOTE: Limits stack to 2GB on 32-bit platforms.
        assert!(max_capacity < isize::MAX as usize);
        let layout = Layout::from_size_align(max_capacity, 16).unwrap();
        let layout = layout.pad_to_align();
        let data = unsafe { alloc(layout) };
        let locked = Cell::new(false);
        Self {
            data,
            layout,
            locked,
        }
    }

    pub fn unwrap_with_lock<F>(&self, func: F)
        where F : for<'b> FnOnce(Stack<'b>)
    {
        func(self.try_lock().unwrap());
        self.locked.set(false);
    }

    pub fn try_lock<'a>(&'a self) -> Option<Stack<'a>> {
        if self.locked.get() {
            return None;
        }

        self.locked.set(true);
        let ptr = self.data.wrapping_add(self.layout.size());
        let stack = Stack {
            owner: self,
            ptr: Cell::new(NonNull::new(ptr).unwrap()),
            _phantom: PhantomData,
        };
        Some(stack)
    }

    #[inline(always)]
    unsafe fn try_alloc_layout(&self, ptr: NonNull<u8>, layout: Layout) -> Option<NonNull<u8>> {
        assert!(self.locked.get());
        let base = self.data;
        let ptr = ptr.as_ptr();
        if (ptr as usize) < layout.size() {
            return None;
        }

        let ptr = ptr.wrapping_sub(layout.size());
        let aligned_ptr = ptr.wrapping_sub((ptr as usize) % layout.align());
        if aligned_ptr < base {
            return None;
        }

        Some(NonNull::new_unchecked(aligned_ptr))
    }

    #[inline(always)]
    unsafe fn alloc_layout(&self, ptr: NonNull<u8>, layout: Layout) -> NonNull<u8> {
        self.try_alloc_layout(ptr, layout).unwrap_or_else(|| oom())
    }
}

impl Drop for StackMemory {
    fn drop(&mut self) {
        unsafe {
            dealloc(self.data, self.layout);
        }
    }
}

pub struct Stack<'a> {
    owner: &'a StackMemory,
    ptr: Cell<NonNull<u8>>,
    _phantom: PhantomData<&'a mut [MaybeUninit<u8>]>,
}

impl<'a> Stack<'a> {
    // Mutable in order to make sure that within a scope we can only allocate a single new scope.
    #[inline(always)]
    pub fn scope<'short>(&'short mut self) -> Stack<'short>
    where
        'a: 'short,
    {
        Stack {
            owner: self.owner,
            ptr: Cell::new(self.ptr.get()),
            _phantom: PhantomData::default(),
        }
    }

    #[inline(always)]
    pub fn try_alloc<T>(&self, value: T) -> Option<&T> {
        let layout = Layout::new::<T>();
        unsafe {
            let ptr = self.owner.try_alloc_layout(self.ptr.get(), layout)?;
            std::ptr::write(ptr.cast().as_ptr(), value);
            self.ptr.set(ptr);
            Some(&*ptr.cast().as_ptr())
        }
    }

    #[inline(always)]
    pub fn alloc<T>(&self, value: T) -> &T {
        self.try_alloc(value).unwrap_or_else(|| oom())
    }

    #[inline(always)]
    pub fn alloc_slice_fill_iter<T, I>(&self, iter: I) -> &mut [T]
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let mut iter = iter.into_iter();
        let len = iter.len();
        let layout = Layout::array::<T>(len).unwrap();
        unsafe {
            let ptr = self.owner.alloc_layout(self.ptr.get(), layout);
            self.ptr.set(ptr);
            let ptr = ptr.cast::<T>().as_ptr();
            for i in 0..len {
                std::ptr::write(ptr.add(i), iter.next().unwrap());
            }

            std::slice::from_raw_parts_mut(ptr, len)
        }
    }
}

mod test {

    #[test]
    fn test_double_lock() {
        let mem = super::StackMemory::new(32);
        let stack = mem.try_lock();
        assert!(stack.is_some());
        let stack2 = mem.try_lock();
        assert!(stack2.is_none());
    }

    #[test]
    fn test_oom() {
        let num = 1024usize;
        let mem = super::StackMemory::new(num as usize * std::mem::size_of::<usize>());
        let stack = mem.try_lock().unwrap();
        for i in 0..num {
            assert_eq!(stack.alloc(i), &i);
        }

        // NOTE: alignments here should guarantee that there isn't more space
        assert!(stack.try_alloc(0).is_none());
    }

    #[test]
    fn test_simple() {
        let num = 1024usize;
        let mem = super::StackMemory::new(num as usize * std::mem::size_of::<usize>());
        let stack = mem.try_lock().unwrap();
        let mut vec: Vec<&usize> = Vec::new();
        for i in 0..num {
            vec.push(stack.alloc(i));
        }

        for i in 0..num {
            assert_eq!(vec[i], &i);
        }
    }

    #[test]
    fn test_iter() {
        let mem = super::StackMemory::new(1024 * 1024);
        let stack = mem.try_lock().unwrap();
        let slice = stack.alloc_slice_fill_iter(0..100);
        assert_eq!(slice, (0..100).collect::<Vec<_>>());
    }

    #[test]
    fn test_nest() {
        let num = 16u16;
        let mem = super::StackMemory::new(num as usize * std::mem::size_of::<u16>());
        let mut stack = mem.try_lock().unwrap();
        for i in 0..num {
            let substack = stack.scope();
            for j in 0..num {
                let k = i + j;
                assert_eq!(substack.alloc(k), &k);
            }
        }
    }

    #[test]
    fn test_sandwich() {
        let mem = super::StackMemory::new(1024);
        let mut stack = mem.try_lock().unwrap();
        // Can allocate but can not have references overlap new scopes.
        assert_eq!(stack.alloc(0), &0);
        {
            let substack = stack.scope();
            assert_eq!(substack.alloc(1), &1);
        }
        assert_eq!(stack.alloc(2), &2);
        {
            let substack = stack.scope();
            assert_eq!(substack.alloc(3), &3);
        }
        assert_eq!(stack.alloc(4), &4);
    }

    #[test]
    fn test_alloc_struct() {
        #[derive(Debug, Clone, PartialEq)]
        struct Test {
            x: usize,
            y: [bool; 10],
            z: (u8, u16, u32, u64),
            w: &'static str,
        }

        let value = Test {
            x: 1,
            y: [true; 10],
            z: (2, 3, 4, 5),
            w: "hello",
        };
        let mem = super::StackMemory::new(1024);
        let stack = mem.try_lock().unwrap();
        let mut ref_vec: Vec<&Test> = Vec::new();
        for _ in 0..10 {
            let value_ref = stack.alloc(value.clone());
            assert_eq!(value_ref, &value);
            ref_vec.push(value_ref);
        }

        for i in 1..ref_vec.len() {
            assert!(!std::ptr::eq(ref_vec[i - 1], ref_vec[i]));
        }
    }
}
