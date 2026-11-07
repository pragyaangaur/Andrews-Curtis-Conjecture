import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 155 of the cap-17 certificate: slots 79360 .. 79871 -/
theorem chk_155 : chunkCheck 17 T stdSt 79360 512 = true := by decide +kernel

end Row17
