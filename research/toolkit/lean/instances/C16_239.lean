import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 239 of the cap-16 certificate: slots 244736 .. 245759 -/
theorem chk_239 : chunkCheck 16 T stdSt 244736 1024 = true := by decide +kernel

end Row16
