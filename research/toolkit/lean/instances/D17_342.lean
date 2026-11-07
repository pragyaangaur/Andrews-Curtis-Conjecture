import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 342 of the cap-17 certificate: slots 175104 .. 175615 -/
theorem chk_342 : chunkCheck 17 T stdSt 175104 512 = true := by decide +kernel

end Row17
