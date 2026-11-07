import RowBase_16
import C16_0
import C16_1
import C16_2
import C16_3
import C16_4
import C16_5
import C16_6
import C16_7
import C16_8
import C16_9
import C16_10
import C16_11
import C16_12
import C16_13
import C16_14
import C16_15
import C16_16
import C16_17
import C16_18
import C16_19
import C16_20
import C16_21
import C16_22
import C16_23
import C16_24
import C16_25
import C16_26
import C16_27
import C16_28
import C16_29
import C16_30
import C16_31
import C16_32
import C16_33
import C16_34
import C16_35
import C16_36
import C16_37
import C16_38
import C16_39
import C16_40
import C16_41
import C16_42
import C16_43
import C16_44
import C16_45
import C16_46
import C16_47
import C16_48
import C16_49
import C16_50
import C16_51
import C16_52
import C16_53
import C16_54
import C16_55
import C16_56
import C16_57
import C16_58
import C16_59
import C16_60
import C16_61
import C16_62
import C16_63
import C16_64
import C16_65
import C16_66
import C16_67
import C16_68
import C16_69
import C16_70
import C16_71
import C16_72
import C16_73
import C16_74
import C16_75
import C16_76
import C16_77
import C16_78
import C16_79
import C16_80
import C16_81
import C16_82
import C16_83
import C16_84
import C16_85
import C16_86
import C16_87
import C16_88
import C16_89
import C16_90
import C16_91
import C16_92
import C16_93
import C16_94
import C16_95
import C16_96
import C16_97
import C16_98
import C16_99
import C16_100
import C16_101
import C16_102
import C16_103
import C16_104
import C16_105
import C16_106
import C16_107
import C16_108
import C16_109
import C16_110
import C16_111
import C16_112
import C16_113
import C16_114
import C16_115
import C16_116
import C16_117
import C16_118
import C16_119
import C16_120
import C16_121
import C16_122
import C16_123
import C16_124
import C16_125
import C16_126
import C16_127
import C16_128
import C16_129
import C16_130
import C16_131
import C16_132
import C16_133
import C16_134
import C16_135
import C16_136
import C16_137
import C16_138
import C16_139
import C16_140
import C16_141
import C16_142
import C16_143
import C16_144
import C16_145
import C16_146
import C16_147
import C16_148
import C16_149
import C16_150
import C16_151
import C16_152
import C16_153
import C16_154
import C16_155
import C16_156
import C16_157
import C16_158
import C16_159
import C16_160
import C16_161
import C16_162
import C16_163
import C16_164
import C16_165
import C16_166
import C16_167
import C16_168
import C16_169
import C16_170
import C16_171
import C16_172
import C16_173
import C16_174
import C16_175
import C16_176
import C16_177
import C16_178
import C16_179
import C16_180
import C16_181
import C16_182
import C16_183
import C16_184
import C16_185
import C16_186
import C16_187
import C16_188
import C16_189
import C16_190
import C16_191
import C16_192
import C16_193
import C16_194
import C16_195
import C16_196
import C16_197
import C16_198
import C16_199
import C16_200
import C16_201
import C16_202
import C16_203
import C16_204
import C16_205
import C16_206
import C16_207
import C16_208
import C16_209
import C16_210
import C16_211
import C16_212
import C16_213
import C16_214
import C16_215
import C16_216
import C16_217
import C16_218
import C16_219
import C16_220
import C16_221
import C16_222
import C16_223
import C16_224
import C16_225
import C16_226
import C16_227
import C16_228
import C16_229
import C16_230
import C16_231
import C16_232
import C16_233
import C16_234
import C16_235
import C16_236
import C16_237
import C16_238
import C16_239
import C16_240
import C16_241
import C16_242
import C16_243
import C16_244
import C16_245
import C16_246
import C16_247
import C16_248
import C16_249
import C16_250
import C16_251
import C16_252
import C16_253
import C16_254
import C16_255

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

theorem s1_0 : chunkCheck 16 T stdSt 0 (1024 + 1024) = true := chunkCheck_append chk_0 chk_1
theorem s1_1 : chunkCheck 16 T stdSt 2048 (1024 + 1024) = true := chunkCheck_append chk_2 chk_3
theorem s1_2 : chunkCheck 16 T stdSt 4096 (1024 + 1024) = true := chunkCheck_append chk_4 chk_5
theorem s1_3 : chunkCheck 16 T stdSt 6144 (1024 + 1024) = true := chunkCheck_append chk_6 chk_7
theorem s1_4 : chunkCheck 16 T stdSt 8192 (1024 + 1024) = true := chunkCheck_append chk_8 chk_9
theorem s1_5 : chunkCheck 16 T stdSt 10240 (1024 + 1024) = true := chunkCheck_append chk_10 chk_11
theorem s1_6 : chunkCheck 16 T stdSt 12288 (1024 + 1024) = true := chunkCheck_append chk_12 chk_13
theorem s1_7 : chunkCheck 16 T stdSt 14336 (1024 + 1024) = true := chunkCheck_append chk_14 chk_15
theorem s1_8 : chunkCheck 16 T stdSt 16384 (1024 + 1024) = true := chunkCheck_append chk_16 chk_17
theorem s1_9 : chunkCheck 16 T stdSt 18432 (1024 + 1024) = true := chunkCheck_append chk_18 chk_19
theorem s1_10 : chunkCheck 16 T stdSt 20480 (1024 + 1024) = true := chunkCheck_append chk_20 chk_21
theorem s1_11 : chunkCheck 16 T stdSt 22528 (1024 + 1024) = true := chunkCheck_append chk_22 chk_23
theorem s1_12 : chunkCheck 16 T stdSt 24576 (1024 + 1024) = true := chunkCheck_append chk_24 chk_25
theorem s1_13 : chunkCheck 16 T stdSt 26624 (1024 + 1024) = true := chunkCheck_append chk_26 chk_27
theorem s1_14 : chunkCheck 16 T stdSt 28672 (1024 + 1024) = true := chunkCheck_append chk_28 chk_29
theorem s1_15 : chunkCheck 16 T stdSt 30720 (1024 + 1024) = true := chunkCheck_append chk_30 chk_31
theorem s1_16 : chunkCheck 16 T stdSt 32768 (1024 + 1024) = true := chunkCheck_append chk_32 chk_33
theorem s1_17 : chunkCheck 16 T stdSt 34816 (1024 + 1024) = true := chunkCheck_append chk_34 chk_35
theorem s1_18 : chunkCheck 16 T stdSt 36864 (1024 + 1024) = true := chunkCheck_append chk_36 chk_37
theorem s1_19 : chunkCheck 16 T stdSt 38912 (1024 + 1024) = true := chunkCheck_append chk_38 chk_39
theorem s1_20 : chunkCheck 16 T stdSt 40960 (1024 + 1024) = true := chunkCheck_append chk_40 chk_41
theorem s1_21 : chunkCheck 16 T stdSt 43008 (1024 + 1024) = true := chunkCheck_append chk_42 chk_43
theorem s1_22 : chunkCheck 16 T stdSt 45056 (1024 + 1024) = true := chunkCheck_append chk_44 chk_45
theorem s1_23 : chunkCheck 16 T stdSt 47104 (1024 + 1024) = true := chunkCheck_append chk_46 chk_47
theorem s1_24 : chunkCheck 16 T stdSt 49152 (1024 + 1024) = true := chunkCheck_append chk_48 chk_49
theorem s1_25 : chunkCheck 16 T stdSt 51200 (1024 + 1024) = true := chunkCheck_append chk_50 chk_51
theorem s1_26 : chunkCheck 16 T stdSt 53248 (1024 + 1024) = true := chunkCheck_append chk_52 chk_53
theorem s1_27 : chunkCheck 16 T stdSt 55296 (1024 + 1024) = true := chunkCheck_append chk_54 chk_55
theorem s1_28 : chunkCheck 16 T stdSt 57344 (1024 + 1024) = true := chunkCheck_append chk_56 chk_57
theorem s1_29 : chunkCheck 16 T stdSt 59392 (1024 + 1024) = true := chunkCheck_append chk_58 chk_59
theorem s1_30 : chunkCheck 16 T stdSt 61440 (1024 + 1024) = true := chunkCheck_append chk_60 chk_61
theorem s1_31 : chunkCheck 16 T stdSt 63488 (1024 + 1024) = true := chunkCheck_append chk_62 chk_63
theorem s1_32 : chunkCheck 16 T stdSt 65536 (1024 + 1024) = true := chunkCheck_append chk_64 chk_65
theorem s1_33 : chunkCheck 16 T stdSt 67584 (1024 + 1024) = true := chunkCheck_append chk_66 chk_67
theorem s1_34 : chunkCheck 16 T stdSt 69632 (1024 + 1024) = true := chunkCheck_append chk_68 chk_69
theorem s1_35 : chunkCheck 16 T stdSt 71680 (1024 + 1024) = true := chunkCheck_append chk_70 chk_71
theorem s1_36 : chunkCheck 16 T stdSt 73728 (1024 + 1024) = true := chunkCheck_append chk_72 chk_73
theorem s1_37 : chunkCheck 16 T stdSt 75776 (1024 + 1024) = true := chunkCheck_append chk_74 chk_75
theorem s1_38 : chunkCheck 16 T stdSt 77824 (1024 + 1024) = true := chunkCheck_append chk_76 chk_77
theorem s1_39 : chunkCheck 16 T stdSt 79872 (1024 + 1024) = true := chunkCheck_append chk_78 chk_79
theorem s1_40 : chunkCheck 16 T stdSt 81920 (1024 + 1024) = true := chunkCheck_append chk_80 chk_81
theorem s1_41 : chunkCheck 16 T stdSt 83968 (1024 + 1024) = true := chunkCheck_append chk_82 chk_83
theorem s1_42 : chunkCheck 16 T stdSt 86016 (1024 + 1024) = true := chunkCheck_append chk_84 chk_85
theorem s1_43 : chunkCheck 16 T stdSt 88064 (1024 + 1024) = true := chunkCheck_append chk_86 chk_87
theorem s1_44 : chunkCheck 16 T stdSt 90112 (1024 + 1024) = true := chunkCheck_append chk_88 chk_89
theorem s1_45 : chunkCheck 16 T stdSt 92160 (1024 + 1024) = true := chunkCheck_append chk_90 chk_91
theorem s1_46 : chunkCheck 16 T stdSt 94208 (1024 + 1024) = true := chunkCheck_append chk_92 chk_93
theorem s1_47 : chunkCheck 16 T stdSt 96256 (1024 + 1024) = true := chunkCheck_append chk_94 chk_95
theorem s1_48 : chunkCheck 16 T stdSt 98304 (1024 + 1024) = true := chunkCheck_append chk_96 chk_97
theorem s1_49 : chunkCheck 16 T stdSt 100352 (1024 + 1024) = true := chunkCheck_append chk_98 chk_99
theorem s1_50 : chunkCheck 16 T stdSt 102400 (1024 + 1024) = true := chunkCheck_append chk_100 chk_101
theorem s1_51 : chunkCheck 16 T stdSt 104448 (1024 + 1024) = true := chunkCheck_append chk_102 chk_103
theorem s1_52 : chunkCheck 16 T stdSt 106496 (1024 + 1024) = true := chunkCheck_append chk_104 chk_105
theorem s1_53 : chunkCheck 16 T stdSt 108544 (1024 + 1024) = true := chunkCheck_append chk_106 chk_107
theorem s1_54 : chunkCheck 16 T stdSt 110592 (1024 + 1024) = true := chunkCheck_append chk_108 chk_109
theorem s1_55 : chunkCheck 16 T stdSt 112640 (1024 + 1024) = true := chunkCheck_append chk_110 chk_111
theorem s1_56 : chunkCheck 16 T stdSt 114688 (1024 + 1024) = true := chunkCheck_append chk_112 chk_113
theorem s1_57 : chunkCheck 16 T stdSt 116736 (1024 + 1024) = true := chunkCheck_append chk_114 chk_115
theorem s1_58 : chunkCheck 16 T stdSt 118784 (1024 + 1024) = true := chunkCheck_append chk_116 chk_117
theorem s1_59 : chunkCheck 16 T stdSt 120832 (1024 + 1024) = true := chunkCheck_append chk_118 chk_119
theorem s1_60 : chunkCheck 16 T stdSt 122880 (1024 + 1024) = true := chunkCheck_append chk_120 chk_121
theorem s1_61 : chunkCheck 16 T stdSt 124928 (1024 + 1024) = true := chunkCheck_append chk_122 chk_123
theorem s1_62 : chunkCheck 16 T stdSt 126976 (1024 + 1024) = true := chunkCheck_append chk_124 chk_125
theorem s1_63 : chunkCheck 16 T stdSt 129024 (1024 + 1024) = true := chunkCheck_append chk_126 chk_127
theorem s1_64 : chunkCheck 16 T stdSt 131072 (1024 + 1024) = true := chunkCheck_append chk_128 chk_129
theorem s1_65 : chunkCheck 16 T stdSt 133120 (1024 + 1024) = true := chunkCheck_append chk_130 chk_131
theorem s1_66 : chunkCheck 16 T stdSt 135168 (1024 + 1024) = true := chunkCheck_append chk_132 chk_133
theorem s1_67 : chunkCheck 16 T stdSt 137216 (1024 + 1024) = true := chunkCheck_append chk_134 chk_135
theorem s1_68 : chunkCheck 16 T stdSt 139264 (1024 + 1024) = true := chunkCheck_append chk_136 chk_137
theorem s1_69 : chunkCheck 16 T stdSt 141312 (1024 + 1024) = true := chunkCheck_append chk_138 chk_139
theorem s1_70 : chunkCheck 16 T stdSt 143360 (1024 + 1024) = true := chunkCheck_append chk_140 chk_141
theorem s1_71 : chunkCheck 16 T stdSt 145408 (1024 + 1024) = true := chunkCheck_append chk_142 chk_143
theorem s1_72 : chunkCheck 16 T stdSt 147456 (1024 + 1024) = true := chunkCheck_append chk_144 chk_145
theorem s1_73 : chunkCheck 16 T stdSt 149504 (1024 + 1024) = true := chunkCheck_append chk_146 chk_147
theorem s1_74 : chunkCheck 16 T stdSt 151552 (1024 + 1024) = true := chunkCheck_append chk_148 chk_149
theorem s1_75 : chunkCheck 16 T stdSt 153600 (1024 + 1024) = true := chunkCheck_append chk_150 chk_151
theorem s1_76 : chunkCheck 16 T stdSt 155648 (1024 + 1024) = true := chunkCheck_append chk_152 chk_153
theorem s1_77 : chunkCheck 16 T stdSt 157696 (1024 + 1024) = true := chunkCheck_append chk_154 chk_155
theorem s1_78 : chunkCheck 16 T stdSt 159744 (1024 + 1024) = true := chunkCheck_append chk_156 chk_157
theorem s1_79 : chunkCheck 16 T stdSt 161792 (1024 + 1024) = true := chunkCheck_append chk_158 chk_159
theorem s1_80 : chunkCheck 16 T stdSt 163840 (1024 + 1024) = true := chunkCheck_append chk_160 chk_161
theorem s1_81 : chunkCheck 16 T stdSt 165888 (1024 + 1024) = true := chunkCheck_append chk_162 chk_163
theorem s1_82 : chunkCheck 16 T stdSt 167936 (1024 + 1024) = true := chunkCheck_append chk_164 chk_165
theorem s1_83 : chunkCheck 16 T stdSt 169984 (1024 + 1024) = true := chunkCheck_append chk_166 chk_167
theorem s1_84 : chunkCheck 16 T stdSt 172032 (1024 + 1024) = true := chunkCheck_append chk_168 chk_169
theorem s1_85 : chunkCheck 16 T stdSt 174080 (1024 + 1024) = true := chunkCheck_append chk_170 chk_171
theorem s1_86 : chunkCheck 16 T stdSt 176128 (1024 + 1024) = true := chunkCheck_append chk_172 chk_173
theorem s1_87 : chunkCheck 16 T stdSt 178176 (1024 + 1024) = true := chunkCheck_append chk_174 chk_175
theorem s1_88 : chunkCheck 16 T stdSt 180224 (1024 + 1024) = true := chunkCheck_append chk_176 chk_177
theorem s1_89 : chunkCheck 16 T stdSt 182272 (1024 + 1024) = true := chunkCheck_append chk_178 chk_179
theorem s1_90 : chunkCheck 16 T stdSt 184320 (1024 + 1024) = true := chunkCheck_append chk_180 chk_181
theorem s1_91 : chunkCheck 16 T stdSt 186368 (1024 + 1024) = true := chunkCheck_append chk_182 chk_183
theorem s1_92 : chunkCheck 16 T stdSt 188416 (1024 + 1024) = true := chunkCheck_append chk_184 chk_185
theorem s1_93 : chunkCheck 16 T stdSt 190464 (1024 + 1024) = true := chunkCheck_append chk_186 chk_187
theorem s1_94 : chunkCheck 16 T stdSt 192512 (1024 + 1024) = true := chunkCheck_append chk_188 chk_189
theorem s1_95 : chunkCheck 16 T stdSt 194560 (1024 + 1024) = true := chunkCheck_append chk_190 chk_191
theorem s1_96 : chunkCheck 16 T stdSt 196608 (1024 + 1024) = true := chunkCheck_append chk_192 chk_193
theorem s1_97 : chunkCheck 16 T stdSt 198656 (1024 + 1024) = true := chunkCheck_append chk_194 chk_195
theorem s1_98 : chunkCheck 16 T stdSt 200704 (1024 + 1024) = true := chunkCheck_append chk_196 chk_197
theorem s1_99 : chunkCheck 16 T stdSt 202752 (1024 + 1024) = true := chunkCheck_append chk_198 chk_199
theorem s1_100 : chunkCheck 16 T stdSt 204800 (1024 + 1024) = true := chunkCheck_append chk_200 chk_201
theorem s1_101 : chunkCheck 16 T stdSt 206848 (1024 + 1024) = true := chunkCheck_append chk_202 chk_203
theorem s1_102 : chunkCheck 16 T stdSt 208896 (1024 + 1024) = true := chunkCheck_append chk_204 chk_205
theorem s1_103 : chunkCheck 16 T stdSt 210944 (1024 + 1024) = true := chunkCheck_append chk_206 chk_207
theorem s1_104 : chunkCheck 16 T stdSt 212992 (1024 + 1024) = true := chunkCheck_append chk_208 chk_209
theorem s1_105 : chunkCheck 16 T stdSt 215040 (1024 + 1024) = true := chunkCheck_append chk_210 chk_211
theorem s1_106 : chunkCheck 16 T stdSt 217088 (1024 + 1024) = true := chunkCheck_append chk_212 chk_213
theorem s1_107 : chunkCheck 16 T stdSt 219136 (1024 + 1024) = true := chunkCheck_append chk_214 chk_215
theorem s1_108 : chunkCheck 16 T stdSt 221184 (1024 + 1024) = true := chunkCheck_append chk_216 chk_217
theorem s1_109 : chunkCheck 16 T stdSt 223232 (1024 + 1024) = true := chunkCheck_append chk_218 chk_219
theorem s1_110 : chunkCheck 16 T stdSt 225280 (1024 + 1024) = true := chunkCheck_append chk_220 chk_221
theorem s1_111 : chunkCheck 16 T stdSt 227328 (1024 + 1024) = true := chunkCheck_append chk_222 chk_223
theorem s1_112 : chunkCheck 16 T stdSt 229376 (1024 + 1024) = true := chunkCheck_append chk_224 chk_225
theorem s1_113 : chunkCheck 16 T stdSt 231424 (1024 + 1024) = true := chunkCheck_append chk_226 chk_227
theorem s1_114 : chunkCheck 16 T stdSt 233472 (1024 + 1024) = true := chunkCheck_append chk_228 chk_229
theorem s1_115 : chunkCheck 16 T stdSt 235520 (1024 + 1024) = true := chunkCheck_append chk_230 chk_231
theorem s1_116 : chunkCheck 16 T stdSt 237568 (1024 + 1024) = true := chunkCheck_append chk_232 chk_233
theorem s1_117 : chunkCheck 16 T stdSt 239616 (1024 + 1024) = true := chunkCheck_append chk_234 chk_235
theorem s1_118 : chunkCheck 16 T stdSt 241664 (1024 + 1024) = true := chunkCheck_append chk_236 chk_237
theorem s1_119 : chunkCheck 16 T stdSt 243712 (1024 + 1024) = true := chunkCheck_append chk_238 chk_239
theorem s1_120 : chunkCheck 16 T stdSt 245760 (1024 + 1024) = true := chunkCheck_append chk_240 chk_241
theorem s1_121 : chunkCheck 16 T stdSt 247808 (1024 + 1024) = true := chunkCheck_append chk_242 chk_243
theorem s1_122 : chunkCheck 16 T stdSt 249856 (1024 + 1024) = true := chunkCheck_append chk_244 chk_245
theorem s1_123 : chunkCheck 16 T stdSt 251904 (1024 + 1024) = true := chunkCheck_append chk_246 chk_247
theorem s1_124 : chunkCheck 16 T stdSt 253952 (1024 + 1024) = true := chunkCheck_append chk_248 chk_249
theorem s1_125 : chunkCheck 16 T stdSt 256000 (1024 + 1024) = true := chunkCheck_append chk_250 chk_251
theorem s1_126 : chunkCheck 16 T stdSt 258048 (1024 + 1024) = true := chunkCheck_append chk_252 chk_253
theorem s1_127 : chunkCheck 16 T stdSt 260096 (1024 + 1024) = true := chunkCheck_append chk_254 chk_255
theorem s2_0 : chunkCheck 16 T stdSt 0 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_0 s1_1
theorem s2_1 : chunkCheck 16 T stdSt 4096 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_2 s1_3
theorem s2_2 : chunkCheck 16 T stdSt 8192 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_4 s1_5
theorem s2_3 : chunkCheck 16 T stdSt 12288 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_6 s1_7
theorem s2_4 : chunkCheck 16 T stdSt 16384 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_8 s1_9
theorem s2_5 : chunkCheck 16 T stdSt 20480 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_10 s1_11
theorem s2_6 : chunkCheck 16 T stdSt 24576 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_12 s1_13
theorem s2_7 : chunkCheck 16 T stdSt 28672 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_14 s1_15
theorem s2_8 : chunkCheck 16 T stdSt 32768 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_16 s1_17
theorem s2_9 : chunkCheck 16 T stdSt 36864 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_18 s1_19
theorem s2_10 : chunkCheck 16 T stdSt 40960 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_20 s1_21
theorem s2_11 : chunkCheck 16 T stdSt 45056 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_22 s1_23
theorem s2_12 : chunkCheck 16 T stdSt 49152 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_24 s1_25
theorem s2_13 : chunkCheck 16 T stdSt 53248 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_26 s1_27
theorem s2_14 : chunkCheck 16 T stdSt 57344 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_28 s1_29
theorem s2_15 : chunkCheck 16 T stdSt 61440 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_30 s1_31
theorem s2_16 : chunkCheck 16 T stdSt 65536 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_32 s1_33
theorem s2_17 : chunkCheck 16 T stdSt 69632 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_34 s1_35
theorem s2_18 : chunkCheck 16 T stdSt 73728 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_36 s1_37
theorem s2_19 : chunkCheck 16 T stdSt 77824 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_38 s1_39
theorem s2_20 : chunkCheck 16 T stdSt 81920 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_40 s1_41
theorem s2_21 : chunkCheck 16 T stdSt 86016 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_42 s1_43
theorem s2_22 : chunkCheck 16 T stdSt 90112 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_44 s1_45
theorem s2_23 : chunkCheck 16 T stdSt 94208 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_46 s1_47
theorem s2_24 : chunkCheck 16 T stdSt 98304 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_48 s1_49
theorem s2_25 : chunkCheck 16 T stdSt 102400 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_50 s1_51
theorem s2_26 : chunkCheck 16 T stdSt 106496 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_52 s1_53
theorem s2_27 : chunkCheck 16 T stdSt 110592 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_54 s1_55
theorem s2_28 : chunkCheck 16 T stdSt 114688 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_56 s1_57
theorem s2_29 : chunkCheck 16 T stdSt 118784 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_58 s1_59
theorem s2_30 : chunkCheck 16 T stdSt 122880 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_60 s1_61
theorem s2_31 : chunkCheck 16 T stdSt 126976 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_62 s1_63
theorem s2_32 : chunkCheck 16 T stdSt 131072 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_64 s1_65
theorem s2_33 : chunkCheck 16 T stdSt 135168 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_66 s1_67
theorem s2_34 : chunkCheck 16 T stdSt 139264 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_68 s1_69
theorem s2_35 : chunkCheck 16 T stdSt 143360 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_70 s1_71
theorem s2_36 : chunkCheck 16 T stdSt 147456 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_72 s1_73
theorem s2_37 : chunkCheck 16 T stdSt 151552 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_74 s1_75
theorem s2_38 : chunkCheck 16 T stdSt 155648 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_76 s1_77
theorem s2_39 : chunkCheck 16 T stdSt 159744 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_78 s1_79
theorem s2_40 : chunkCheck 16 T stdSt 163840 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_80 s1_81
theorem s2_41 : chunkCheck 16 T stdSt 167936 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_82 s1_83
theorem s2_42 : chunkCheck 16 T stdSt 172032 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_84 s1_85
theorem s2_43 : chunkCheck 16 T stdSt 176128 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_86 s1_87
theorem s2_44 : chunkCheck 16 T stdSt 180224 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_88 s1_89
theorem s2_45 : chunkCheck 16 T stdSt 184320 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_90 s1_91
theorem s2_46 : chunkCheck 16 T stdSt 188416 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_92 s1_93
theorem s2_47 : chunkCheck 16 T stdSt 192512 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_94 s1_95
theorem s2_48 : chunkCheck 16 T stdSt 196608 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_96 s1_97
theorem s2_49 : chunkCheck 16 T stdSt 200704 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_98 s1_99
theorem s2_50 : chunkCheck 16 T stdSt 204800 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_100 s1_101
theorem s2_51 : chunkCheck 16 T stdSt 208896 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_102 s1_103
theorem s2_52 : chunkCheck 16 T stdSt 212992 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_104 s1_105
theorem s2_53 : chunkCheck 16 T stdSt 217088 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_106 s1_107
theorem s2_54 : chunkCheck 16 T stdSt 221184 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_108 s1_109
theorem s2_55 : chunkCheck 16 T stdSt 225280 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_110 s1_111
theorem s2_56 : chunkCheck 16 T stdSt 229376 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_112 s1_113
theorem s2_57 : chunkCheck 16 T stdSt 233472 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_114 s1_115
theorem s2_58 : chunkCheck 16 T stdSt 237568 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_116 s1_117
theorem s2_59 : chunkCheck 16 T stdSt 241664 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_118 s1_119
theorem s2_60 : chunkCheck 16 T stdSt 245760 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_120 s1_121
theorem s2_61 : chunkCheck 16 T stdSt 249856 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_122 s1_123
theorem s2_62 : chunkCheck 16 T stdSt 253952 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_124 s1_125
theorem s2_63 : chunkCheck 16 T stdSt 258048 ((1024 + 1024) + (1024 + 1024)) = true := chunkCheck_append s1_126 s1_127
theorem s3_0 : chunkCheck 16 T stdSt 0 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_0 s2_1
theorem s3_1 : chunkCheck 16 T stdSt 8192 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_2 s2_3
theorem s3_2 : chunkCheck 16 T stdSt 16384 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_4 s2_5
theorem s3_3 : chunkCheck 16 T stdSt 24576 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_6 s2_7
theorem s3_4 : chunkCheck 16 T stdSt 32768 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_8 s2_9
theorem s3_5 : chunkCheck 16 T stdSt 40960 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_10 s2_11
theorem s3_6 : chunkCheck 16 T stdSt 49152 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_12 s2_13
theorem s3_7 : chunkCheck 16 T stdSt 57344 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_14 s2_15
theorem s3_8 : chunkCheck 16 T stdSt 65536 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_16 s2_17
theorem s3_9 : chunkCheck 16 T stdSt 73728 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_18 s2_19
theorem s3_10 : chunkCheck 16 T stdSt 81920 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_20 s2_21
theorem s3_11 : chunkCheck 16 T stdSt 90112 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_22 s2_23
theorem s3_12 : chunkCheck 16 T stdSt 98304 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_24 s2_25
theorem s3_13 : chunkCheck 16 T stdSt 106496 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_26 s2_27
theorem s3_14 : chunkCheck 16 T stdSt 114688 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_28 s2_29
theorem s3_15 : chunkCheck 16 T stdSt 122880 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_30 s2_31
theorem s3_16 : chunkCheck 16 T stdSt 131072 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_32 s2_33
theorem s3_17 : chunkCheck 16 T stdSt 139264 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_34 s2_35
theorem s3_18 : chunkCheck 16 T stdSt 147456 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_36 s2_37
theorem s3_19 : chunkCheck 16 T stdSt 155648 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_38 s2_39
theorem s3_20 : chunkCheck 16 T stdSt 163840 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_40 s2_41
theorem s3_21 : chunkCheck 16 T stdSt 172032 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_42 s2_43
theorem s3_22 : chunkCheck 16 T stdSt 180224 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_44 s2_45
theorem s3_23 : chunkCheck 16 T stdSt 188416 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_46 s2_47
theorem s3_24 : chunkCheck 16 T stdSt 196608 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_48 s2_49
theorem s3_25 : chunkCheck 16 T stdSt 204800 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_50 s2_51
theorem s3_26 : chunkCheck 16 T stdSt 212992 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_52 s2_53
theorem s3_27 : chunkCheck 16 T stdSt 221184 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_54 s2_55
theorem s3_28 : chunkCheck 16 T stdSt 229376 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_56 s2_57
theorem s3_29 : chunkCheck 16 T stdSt 237568 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_58 s2_59
theorem s3_30 : chunkCheck 16 T stdSt 245760 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_60 s2_61
theorem s3_31 : chunkCheck 16 T stdSt 253952 (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) = true := chunkCheck_append s2_62 s2_63
theorem s4_0 : chunkCheck 16 T stdSt 0 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_0 s3_1
theorem s4_1 : chunkCheck 16 T stdSt 16384 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_2 s3_3
theorem s4_2 : chunkCheck 16 T stdSt 32768 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_4 s3_5
theorem s4_3 : chunkCheck 16 T stdSt 49152 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_6 s3_7
theorem s4_4 : chunkCheck 16 T stdSt 65536 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_8 s3_9
theorem s4_5 : chunkCheck 16 T stdSt 81920 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_10 s3_11
theorem s4_6 : chunkCheck 16 T stdSt 98304 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_12 s3_13
theorem s4_7 : chunkCheck 16 T stdSt 114688 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_14 s3_15
theorem s4_8 : chunkCheck 16 T stdSt 131072 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_16 s3_17
theorem s4_9 : chunkCheck 16 T stdSt 147456 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_18 s3_19
theorem s4_10 : chunkCheck 16 T stdSt 163840 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_20 s3_21
theorem s4_11 : chunkCheck 16 T stdSt 180224 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_22 s3_23
theorem s4_12 : chunkCheck 16 T stdSt 196608 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_24 s3_25
theorem s4_13 : chunkCheck 16 T stdSt 212992 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_26 s3_27
theorem s4_14 : chunkCheck 16 T stdSt 229376 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_28 s3_29
theorem s4_15 : chunkCheck 16 T stdSt 245760 ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) = true := chunkCheck_append s3_30 s3_31
theorem s5_0 : chunkCheck 16 T stdSt 0 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_0 s4_1
theorem s5_1 : chunkCheck 16 T stdSt 32768 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_2 s4_3
theorem s5_2 : chunkCheck 16 T stdSt 65536 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_4 s4_5
theorem s5_3 : chunkCheck 16 T stdSt 98304 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_6 s4_7
theorem s5_4 : chunkCheck 16 T stdSt 131072 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_8 s4_9
theorem s5_5 : chunkCheck 16 T stdSt 163840 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_10 s4_11
theorem s5_6 : chunkCheck 16 T stdSt 196608 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_12 s4_13
theorem s5_7 : chunkCheck 16 T stdSt 229376 (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) = true := chunkCheck_append s4_14 s4_15
theorem s6_0 : chunkCheck 16 T stdSt 0 ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) = true := chunkCheck_append s5_0 s5_1
theorem s6_1 : chunkCheck 16 T stdSt 65536 ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) = true := chunkCheck_append s5_2 s5_3
theorem s6_2 : chunkCheck 16 T stdSt 131072 ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) = true := chunkCheck_append s5_4 s5_5
theorem s6_3 : chunkCheck 16 T stdSt 196608 ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) = true := chunkCheck_append s5_6 s5_7
theorem s7_0 : chunkCheck 16 T stdSt 0 (((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))))) = true := chunkCheck_append s6_0 s6_1
theorem s7_1 : chunkCheck 16 T stdSt 131072 (((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))))) = true := chunkCheck_append s6_2 s6_3
theorem s8_0 : chunkCheck 16 T stdSt 0 ((((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))))) + (((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))))) = true := chunkCheck_append s7_0 s7_1

/-- the root: all 256 chunks combined -/
theorem all16sum : chunkCheck 16 T stdSt 0 ((((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))))) + (((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))))) = true := s8_0

/-- the root length is the whole array -/
theorem rootLen : ((((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))))) + (((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))) + ((((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))))) + (((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))) + ((((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024))) + (((1024 + 1024) + (1024 + 1024)) + ((1024 + 1024) + (1024 + 1024)))))))) = NSLOT := by decide

theorem all16 : chunkCheck 16 T stdSt 0 NSLOT = true := by
  rw [← rootLen]
  exact all16sum

theorem all16_slots : ∀ i, i < NSLOT → slotOK 16 T stdSt i = true := slotOK_of_chunkCheck_all all16

/-- **The cap-16 row theorem**: no move sequence takes the class-C row `BABaba, BBBaBaa`
    to the standard pair with every intermediate of total length at most 16. -/
theorem row_T_c16 : ¬ ∃ ts : List Tok, (∀ i, i ≤ ts.length → totLen (run startSt (ts.take i)) ≤ 16) ∧ run startSt ts = stdSt :=
  not_reach_of_slots (cap := 16) (T := T) (p := startSt) (q := stdSt)
    (by decide) (by decide) (by decide) all16_slots

#print axioms row_T_c16

end Row16
