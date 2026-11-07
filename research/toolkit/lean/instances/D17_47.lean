import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 47 of the cap-17 certificate: slots 24064 .. 24575 -/
theorem chk_47 : chunkCheck 17 T stdSt 24064 512 = true := by decide +kernel

end Row17
