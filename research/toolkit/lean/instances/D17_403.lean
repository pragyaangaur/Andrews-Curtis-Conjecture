import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 403 of the cap-17 certificate: slots 206336 .. 206847 -/
theorem chk_403 : chunkCheck 17 T stdSt 206336 512 = true := by decide +kernel

end Row17
