port 0
port 1
port 66
port 67
port 68
port 69
port 70
port 71
port 72
port 73
port 74
port 75
port 76
port 77
port 78
port 79
port 80
port 81
port 82
port 83
port 84
port 85
port 86
port 87
port 88
port 89
port 90
port 91
port 92
port 93
port 94
port 95
port 96
port 97
port 98
port 99
port 100
port 101
port 102
port 103
port 104
port 105
port 106
port 107
port 108
port 109
port 110
port 111
port 112
port 113
port 114
port 115
port 116
port 117
port 118
port 119
port 120
port 121
port 122
port 123
port 124
port 125
port 126
port 127
port 128
port 129
port 130
port 131
port 132
port 133
port 134
port 135
port 136
port 137
port 138
port 139
port 140
port 141
port 142
port 143
port 144
port 145
port 146
port 147
port 148
port 149
port 150
port 151
port 152
port 153
port 154
port 155
port 156
port 157
port 158
port 159
port 160
port 161
port 162
port 163
port 164
port 165
port 166
port 167
port 168
port 169
port 170
port 171
port 172
port 173
port 174
port 175
port 176
port 177
port 178
port 179
port 180
port 181
port 182
port 183
port 184
port 185
port 186
port 187
port 188
port 189
port 190
port 191
port 192
port 193
port 194
port 195
port 196
port 197
port 198
port 199
port 200
port 201
port 202
port 203
port 204
port 205
port 206
port 207
port 208
port 209
port 210
port 211
port 212
port 213
port 214
port 215
port 216
port 217
port 218
port 219
vec reset 1 1
vec io_imem_resp_valid 1 66
vec io_imem_resp_bits_pc 32 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98
vec io_imem_resp_bits_data 32 99 100 101 102 103 104 105 106 107 108 109 110 111 112 113 114 115 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130
vec io_imem_req_valid 1 1
vec io_imem_req_bits_pc 32 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33
vec io_imem_resp_ready 1 35
vec io_dmem_req_ready 1 135
vec io_dmem_req_valid 1 39
vec io_dmem_req_bits_addr 32 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71
vec io_dmem_req_bits_tag 6 72 73 74 75 76 77
vec io_dmem_req_bits_cmd 4 79 80 81 82
vec io_dmem_req_bits_size 2 84 85
vec io_dmem_s1_kill 1 88
vec io_dmem_s1_data_data 32 89 90 91 92 93 94 95 96 97 98 99 100 101 102 103 104 105 106 107 108 109 110 111 112 113 114 115 116 117 118 119 120
vec io_dmem_resp_valid 1 137
vec io_dmem_resp_bits_tag 7 138 139 140 141 142 143 144
vec io_dmem_resp_bits_data 32 145 146 147 148 149 150 151 152 153 154 155 156 157 158 159 160 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175 176
vec io_dmem_resp_bits_has_data 1 178
vec io_dmem_resp_bits_data_word_bypass 32 179 180 181 182 183 184 185 186 187 188 189 190 191 192 193 194 195 196 197 198 199 200 201 202 203 204 205 206 207 208 209 210
vec io_dmem_ordered 1 218
pattern 0000007f 00000017
pattern 0000007f 00000037
pattern 0000007f 0000006f
pattern 0000707f 0000000f
pattern 0000707f 00000013
pattern 0000707f 00000023
pattern 0000707f 00000063
pattern 0000707f 00000067
pattern 0000707f 00001023
pattern 0000707f 00001063
pattern 0000707f 00002003
pattern 0000707f 00002023
pattern 0000707f 00003013
pattern 0000707f 00004003
pattern 0000707f 00004013
pattern 0000707f 00004063
pattern 0000707f 00005063
pattern fe00707f 00000033
pattern fe00707f 00006033
pattern fe00707f 40000033
pattern ffffffff 00000073
pattern ffffffff 00100073
