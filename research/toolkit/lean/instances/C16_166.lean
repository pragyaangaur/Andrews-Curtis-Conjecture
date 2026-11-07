import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 166 of the cap-16 certificate: slots 169984 .. 171007 -/
theorem chk_166 : chunkCheck 16 T stdSt 169984 1024 = true := by decide +kernel

end Row16
