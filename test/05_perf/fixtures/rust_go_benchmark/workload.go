package main

import (
	"fmt"
	"os"
	"runtime"
	"strconv"
	"strings"
)

func main() {
	raw, err := os.ReadFile(os.Args[1])
	if err != nil {
		panic(err)
	}
	value, err := strconv.ParseInt(strings.TrimSpace(string(raw)), 10, 64)
	if err != nil {
		panic(err)
	}
	for i := 0; i < 100000; i++ {
		value = (value * 48271) % 2147483647
	}
	runtime.KeepAlive(raw)
	fmt.Printf("checksum=%d operations=100000\n", value)
}
