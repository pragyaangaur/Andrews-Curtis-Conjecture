import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 348 of the cap-17 certificate: slots 178176 .. 178687 -/
theorem chk_348 : chunkCheck 17 T stdSt 178176 512 = true := by decide +kernel

end Row17
