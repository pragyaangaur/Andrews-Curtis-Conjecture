import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 362 of the cap-17 certificate: slots 185344 .. 185855 -/
theorem chk_362 : chunkCheck 17 T stdSt 185344 512 = true := by decide +kernel

end Row17
