import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 238 of the cap-17 certificate: slots 121856 .. 122367 -/
theorem chk_238 : chunkCheck 17 T stdSt 121856 512 = true := by decide +kernel

end Row17
