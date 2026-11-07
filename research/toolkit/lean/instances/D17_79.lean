import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 79 of the cap-17 certificate: slots 40448 .. 40959 -/
theorem chk_79 : chunkCheck 17 T stdSt 40448 512 = true := by decide +kernel

end Row17
