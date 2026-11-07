import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 239 of the cap-17 certificate: slots 122368 .. 122879 -/
theorem chk_239 : chunkCheck 17 T stdSt 122368 512 = true := by decide +kernel

end Row17
