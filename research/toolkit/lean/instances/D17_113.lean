import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 113 of the cap-17 certificate: slots 57856 .. 58367 -/
theorem chk_113 : chunkCheck 17 T stdSt 57856 512 = true := by decide +kernel

end Row17
