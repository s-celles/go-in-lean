package p

func F(y int32) int32 {
	return (y >> 1) >> (uint32(1) << 31)
}
