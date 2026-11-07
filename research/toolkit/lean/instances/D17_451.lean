import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 451 of the cap-17 certificate: slots 230912 .. 231423 -/
theorem chk_451 : chunkCheck 17 T stdSt 230912 512 = true := by decide +kernel

end Row17
