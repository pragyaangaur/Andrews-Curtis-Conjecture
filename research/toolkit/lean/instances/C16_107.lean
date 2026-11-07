import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 107 of the cap-16 certificate: slots 109568 .. 110591 -/
theorem chk_107 : chunkCheck 16 T stdSt 109568 1024 = true := by decide +kernel

end Row16
