import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 371 of the cap-17 certificate: slots 189952 .. 190463 -/
theorem chk_371 : chunkCheck 17 T stdSt 189952 512 = true := by decide +kernel

end Row17
