var headstart = 200;
var speed = 5;

$('table').addClass('table well');

var height = parseInt($('#header').css('height'), 10)
$('body').css('padding-top', height);

adjustHeader = function() {
  var scroll = $(window).scrollTop();
  var h = height - scroll;
  $('#header').css('height', h);

  $('.moving-image').each(function() {
  	var pos = $(this).offset().top;
    $(this).children('.moving').css('top', Math.max(0, (pos-(scroll+headstart)) / speed));
  });
}

window.onscroll = adjustHeader
adjustHeader()

collapseNavbar = function() {
  if (parseInt($(window).width(), 10) <= 768) {
    $('.navbar-collapse').collapse('hide');
  } 
}

scrollToHeading = function(id) {
  var height = parseInt($('#header').css('min-height'), 10)
  scrollTo($('#'+id).offset().top - height - 10);
}

scrollTo = function(pos) {
  $('html, body').animate({
    scrollTop: pos
  }, 200); 
}

download = function(url) {
  window.location = url;
}
