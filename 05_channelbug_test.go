package main

import (
	"testing"
	"time"
)

const RESULT = 0

func proc(to time.Duration) int {
	ch := make(chan int)
	go func() {
		// do some processing
		ch <- RESULT
	}()
	select {
	case rslt := <-ch:
		return rslt
	case <-time.After(to):
		return 0
	}
}

// TestTimedOutProcess demonstrates a bug
func TestTimingOutProcess(t *testing.T) {
	_ = proc(1 * time.Second)
}
