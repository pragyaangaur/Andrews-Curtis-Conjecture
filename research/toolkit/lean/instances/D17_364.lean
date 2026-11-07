import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 364 of the cap-17 certificate: slots 186368 .. 186879 -/
theorem chk_364 : chunkCheck 17 T stdSt 186368 512 = true := by decide +kernel

end Row17
