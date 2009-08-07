<head>
  <meta http-equiv="Content-Type" content="text/html;charset=utf-8" />
  <meta http-equiv="Content-Script-Type" content="text/javascript"/>
  <style type="text/css" media="screen,projection">
    @import url('css/blueprint/screen.css');
  </style>
  <style type="text/css" media="print">
    @import url('css/blueprint/print.css');
  </style>
  <style type="text/css">@import url('prettify.css');</style>
  <style type="text/css">@import url('clops.css');</style>
  <script type="text/javascript" src="jquery-1.3.2.min.js"></script>
  <script type="text/javascript" src="jquery.corner.js"></script>
  <script type="text/javascript" src="prettify.js"></script>
  <title>CLOPS reference</title>

  <script  type="text/javascript">
  $(function() { $('.rounded').corner();});
  </script>
</head>

\foreach_option
<a name="\option_anchor"/>
<div class="rounded square colors-2">
  <p><span class="option">\option</span> \option_inline_descr</p>
  \option_descr
\foreach_property
  <div class="rounded square colors-3">
    <p><span class="property">\property</span> \property_inline_descr</p>
    \property_descr
  </div>
\next
</div>
\next
