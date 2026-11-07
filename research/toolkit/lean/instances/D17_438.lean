import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 438 of the cap-17 certificate: slots 224256 .. 224767 -/
theorem chk_438 : chunkCheck 17 T stdSt 224256 512 = true := by decide +kernel

end Row17
