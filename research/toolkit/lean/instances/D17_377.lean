import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 377 of the cap-17 certificate: slots 193024 .. 193535 -/
theorem chk_377 : chunkCheck 17 T stdSt 193024 512 = true := by decide +kernel

end Row17
