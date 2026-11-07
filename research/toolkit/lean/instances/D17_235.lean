import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 235 of the cap-17 certificate: slots 120320 .. 120831 -/
theorem chk_235 : chunkCheck 17 T stdSt 120320 512 = true := by decide +kernel

end Row17
