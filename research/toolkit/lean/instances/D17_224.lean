import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 224 of the cap-17 certificate: slots 114688 .. 115199 -/
theorem chk_224 : chunkCheck 17 T stdSt 114688 512 = true := by decide +kernel

end Row17
