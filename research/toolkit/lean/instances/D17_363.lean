import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 363 of the cap-17 certificate: slots 185856 .. 186367 -/
theorem chk_363 : chunkCheck 17 T stdSt 185856 512 = true := by decide +kernel

end Row17
