import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 508 of the cap-17 certificate: slots 260096 .. 260607 -/
theorem chk_508 : chunkCheck 17 T stdSt 260096 512 = true := by decide +kernel

end Row17
