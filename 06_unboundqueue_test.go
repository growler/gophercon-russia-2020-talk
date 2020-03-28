package main

import (
	"testing"
	"time"
)

func buffer1(inpCh, outCh chan int) {
	var oC chan int
	var out int
	var buf []int
	defer close(outCh)
	for {
		select {
		case inp, ok := <-inpCh:
			if !ok {
				return
			} else if oC != nil {
				buf = append(buf, inp)
			} else {
				out = inp
				oC = outCh
			}
		case oC <- out:
			if len(buf) > 0 {
				out, buf = headtail(buf)
			} else {
				oC = nil
			}
		}
	}
}

func headtail(a []int) (head int, tail []int) {
	head = a[0]
	copy(a, a[1:])
	tail = a[:len(a)-1]
	return
}

func producer(max int, ch chan int) {
	go func() {
		defer close(ch)
		for i := 0; i < max; i++ {
			ch <- i
			time.Sleep(5 * time.Millisecond)
		}
	}()
}

func consumer(ch chan int) (cnt int) {
	for range ch {
		cnt++
	}
	return
}

// TestBuffer1 tests first buffer implementation
func TestBufferBugged(t *testing.T) {
	inp := make(chan int)
	out := make(chan int)
	go buffer1(inp, out)
	producer(10, inp)
	cnt := consumer(out)
	if cnt != 10 {
		t.Errorf("%d\n", cnt)
	}
}
