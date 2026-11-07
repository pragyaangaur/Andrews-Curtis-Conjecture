import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 368 of the cap-17 certificate: slots 188416 .. 188927 -/
theorem chk_368 : chunkCheck 17 T stdSt 188416 512 = true := by decide +kernel

end Row17
