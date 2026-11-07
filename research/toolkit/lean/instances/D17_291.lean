import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 291 of the cap-17 certificate: slots 148992 .. 149503 -/
theorem chk_291 : chunkCheck 17 T stdSt 148992 512 = true := by decide +kernel

end Row17
