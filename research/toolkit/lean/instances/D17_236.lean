import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 236 of the cap-17 certificate: slots 120832 .. 121343 -/
theorem chk_236 : chunkCheck 17 T stdSt 120832 512 = true := by decide +kernel

end Row17
