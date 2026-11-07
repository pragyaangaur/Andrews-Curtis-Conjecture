import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 125 of the cap-17 certificate: slots 64000 .. 64511 -/
theorem chk_125 : chunkCheck 17 T stdSt 64000 512 = true := by decide +kernel

end Row17
