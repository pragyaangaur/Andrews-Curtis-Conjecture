import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 400 of the cap-17 certificate: slots 204800 .. 205311 -/
theorem chk_400 : chunkCheck 17 T stdSt 204800 512 = true := by decide +kernel

end Row17
