import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 500 of the cap-17 certificate: slots 256000 .. 256511 -/
theorem chk_500 : chunkCheck 17 T stdSt 256000 512 = true := by decide +kernel

end Row17
