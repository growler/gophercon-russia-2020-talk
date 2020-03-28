package main

import "testing"

func buffer2(inpCh, outCh chan int) {
	var exit bool
	var oC chan int
	var out int
	var buf []int
	defer close(outCh)
	for {
		select {
		case inp, ok := <-inpCh:
			if !ok {
				if oC == nil {
					return
				} else {
					exit = true
					inpCh = nil
				}
			} else if oC != nil {
				buf = append(buf, inp)
			} else {
				out = inp
				oC = outCh
			}
		case oC <- out:
			if len(buf) > 0 {
				out, buf = headtail(buf)
			} else if !exit {
				oC = nil
			} else {
				return
			}
		}
	}
}

func fastProducer(max int, ch chan int) {
	go func() {
		defer close(ch)
		for i := 0; i < max; i++ {
			ch <- i
		}
	}()
}

func TestExposeBug(t *testing.T) {
	inp := make(chan int)
	out := make(chan int)
	go buffer1(inp, out)
	fastProducer(10, inp)
	cnt := consumer(out)
	if cnt != 10 {
		t.Errorf("%d\n", cnt)
	}
}

// TestBuffer2 demonstrates second buffer implementation
func TestBufferFixed(t *testing.T) {
	inp := make(chan int)
	out := make(chan int)
	go buffer2(inp, out)
	producer(10, inp)
	cnt := consumer(out)
	if cnt != 10 {
		t.Errorf("%d\n", cnt)
	}
}
