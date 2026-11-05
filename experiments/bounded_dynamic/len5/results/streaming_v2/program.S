.option norvc
.option norelax
.section .text
.globl _start
_start:
    li s0, 0x1000
    li s1, 0x2000
    li s2, 64
loop:
    ld a0, 0(s0)
    addi a1, a0, 1
    sd a1, 0(s1)
    addi s0, s0, 8
    addi s1, s1, 8
    addi s2, s2, -1
    bnez s2, loop
    li t0, 0x20000100
    sb zero, 0(t0)
halt:
    j halt
.org 0x1000
    .dword 0x0000000000000000
    .dword 0x9e3779b97f487c15
    .dword 0x3c6ef372fe90f82a
    .dword 0xdaa66d2c7dd9743f
    .dword 0x78dde6e5fd21f054
    .dword 0x1715609f7c7e6c69
    .dword 0xb54cda58fbb2e87e
    .dword 0x538454127b076493
    .dword 0xf1bbcdcbfa43e0a8
    .dword 0x8ff34785798c5cbd
    .dword 0x2e2ac13ef8fcd8d2
    .dword 0xcc623af8782554e7
    .dword 0x6a99b4b1f765d0fc
    .dword 0x08d12e6b76d24d11
    .dword 0xa708a824f60ec926
    .dword 0x454021de7543453b
    .dword 0xe3779b97f487c150
    .dword 0x81af155173d03d65
    .dword 0x1fe68f0af318b97a
    .dword 0xbe1e08c472a1358f
    .dword 0x5c55827df1f9b1a4
    .dword 0xfa8cfc3771362db9
    .dword 0x98c475f0f04aa9ce
    .dword 0x36fbefaa6f9f25e3
    .dword 0xd5336963eecba1f8
    .dword 0x736ae31d6e741e0d
    .dword 0x11a25cd6eda49a22
    .dword 0xafd9d6906ced1637
    .dword 0x4e115049ec1d924c
    .dword 0xec48ca036b4a0e61
    .dword 0x8a8043bcea868a76
    .dword 0x28b7bd766a3b068b
    .dword 0xc6ef372fe90f82a0
    .dword 0x6526b0e968dbfeb5
    .dword 0x035e2aa2e7a07aca
    .dword 0xa195a45c6768f6df
    .dword 0x3fcd1e15e63172f4
    .dword 0xde0497cf6589ef09
    .dword 0x7c3c1188e5426b1e
    .dword 0x1a738b426416e733
    .dword 0xb8ab04fbe3f36348
    .dword 0x56e27eb562bfdf5d
    .dword 0xf519f86ee26c5b72
    .dword 0x9351722861d4d787
    .dword 0x3188ebe1e095539c
    .dword 0xcfc0659b604dcfb1
    .dword 0x6df7df54df3e4bc6
    .dword 0x0c2f590e5ef2c7db
    .dword 0xaa66d2c7dd9743f0
    .dword 0x489e4c815d23c005
    .dword 0xe6d5c63adce83c1a
    .dword 0x850d3ff45bb0b82f
    .dword 0x2344b9addb493444
    .dword 0xc17c33675a01b059
    .dword 0x5fb3ad20d9da2c6e
    .dword 0xfdeb26da596ea883
    .dword 0x9c22a093d83b2498
    .dword 0x3a5a1a4d57e7a0ad
    .dword 0xd8919406d6941cc2
    .dword 0x76c90dc0565c98d7
    .dword 0x15008779d50d14ec
    .dword 0xb338013354c59101
    .dword 0x516f7aecd4760d16
    .dword 0xefa6f4a6532a892b

// Explicitly mapped input RAM padding for speculative reads past the loop.
// It is outside the 64-element application input and is never an output check.
.org 0x1200
    .zero 128
