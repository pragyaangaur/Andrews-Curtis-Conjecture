import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 137 of the cap-17 certificate: slots 70144 .. 70655 -/
theorem chk_137 : chunkCheck 17 T stdSt 70144 512 = true := by decide +kernel

end Row17
