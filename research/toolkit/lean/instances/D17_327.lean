import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 327 of the cap-17 certificate: slots 167424 .. 167935 -/
theorem chk_327 : chunkCheck 17 T stdSt 167424 512 = true := by decide +kernel

end Row17
