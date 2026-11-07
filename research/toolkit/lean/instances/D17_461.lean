import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 461 of the cap-17 certificate: slots 236032 .. 236543 -/
theorem chk_461 : chunkCheck 17 T stdSt 236032 512 = true := by decide +kernel

end Row17
