package main

import "fmt"

//go:noinline
func id(x int64) int64 { return x }

//go:noinline
func f(y int8) int64 {
	v := int16(uint16(y))
	z := id(int64(v))
	if v >= 9 {
		return z + 1000
	}
	return z - 1000
}

func main() {
	fmt.Println(f(-1)) // want -1001; arm64 and ppc64{,le}: 999
}
