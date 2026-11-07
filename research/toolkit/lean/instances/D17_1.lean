import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 1 of the cap-17 certificate: slots 512 .. 1023 -/
theorem chk_1 : chunkCheck 17 T stdSt 512 512 = true := by decide +kernel

end Row17
