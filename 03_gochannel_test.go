package main

import "testing"

type Data struct{}

var MESSAGE = &Data{}

func sender(ch chan *Data) {
	ch <- MESSAGE
	close(ch)
}

func receiver(ch chan *Data) (result *Data) {
	for {
		if r := <-ch; r == nil {
			return
		} else {
			result = r
		}
	}
}

func TestGoChannel(t *testing.T) {
	var ch = make(chan *Data)
	go sender(ch)
	result := receiver(ch)
	if result != MESSAGE {
		t.Errorf("result %v is not %v", result, MESSAGE)
	}
}
