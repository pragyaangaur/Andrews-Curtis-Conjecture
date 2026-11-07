import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 488 of the cap-17 certificate: slots 249856 .. 250367 -/
theorem chk_488 : chunkCheck 17 T stdSt 249856 512 = true := by decide +kernel

end Row17
