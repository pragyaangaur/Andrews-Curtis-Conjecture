import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 333 of the cap-17 certificate: slots 170496 .. 171007 -/
theorem chk_333 : chunkCheck 17 T stdSt 170496 512 = true := by decide +kernel

end Row17
