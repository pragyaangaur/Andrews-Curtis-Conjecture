import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 51 of the cap-17 certificate: slots 26112 .. 26623 -/
theorem chk_51 : chunkCheck 17 T stdSt 26112 512 = true := by decide +kernel

end Row17
